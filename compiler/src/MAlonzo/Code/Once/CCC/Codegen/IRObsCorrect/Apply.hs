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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Apply where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.CCC.Codegen.IRObsCorrect.Apply._.Σ
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.⊤
d_'8868'_17 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.BeforeFrontier
d_BeforeFrontier_696 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun
d_CalleeRun_708 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CellAt
d_CellAt_714 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.EnvAt
d_EnvAt_718 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState
d_FlatState_720 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatSteps
d_FlatSteps_724 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.IRObsCorrectF
d_IRObsCorrectF_736 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_736 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.InputAt
d_InputAt_740 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.MachineRefinesObsF
d_MachineRefinesObsF_746 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ResultPlace
d_ResultPlace_754 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValidAtWF
d_ValidAtWF_764 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized
d_ValueRealized_766 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.chain-events
d_chain'45'events_788 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_chain'45'events_788 ~v0 ~v1 v2 = du_chain'45'events_788 v2
du_chain'45'events_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_chain'45'events_788 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.enter-call
d_enter'45'call_844 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_844 ~v0 ~v1 v2 = du_enter'45'call_844 v2
du_enter'45'call_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_844 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.entry-flat
d_entry'45'flat_848 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_848 ~v0 ~v1 = du_entry'45'flat_848
du_entry'45'flat_848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_848 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
      v1 v2 v3 v4
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.evalᴰ
d_eval'7472'_860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_eval'7472'_860 ~v0 v1 = du_eval'7472'_860 v1
du_eval'7472'_860 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_eval'7472'_860 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_1156
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.eventsAt
d_eventsAt_864 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsAt_864 ~v0 ~v1 = du_eventsAt_864
du_eventsAt_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsAt_864 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_1168
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.find-thunk
d_find'45'thunk_944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_944 ~v0 ~v1 v2 = du_find'45'thunk_944 v2
du_find'45'thunk_944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_944 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.flat-exec-instr
d_flat'45'exec'45'instr_968 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_968 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_968 v2
du_flat'45'exec'45'instr_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_968 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.resultAt
d_resultAt_1144 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_resultAt_1144 ~v0 ~v1 = du_resultAt_1144
du_resultAt_1144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_resultAt_1144 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_1176
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.runAt
d_runAt_1148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runAt_1148 ~v0 ~v1 = du_runAt_1148
du_runAt_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runAt_1148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_runAt_1160
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.stopsAt
d_stopsAt_1196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
d_stopsAt_1196 ~v0 ~v1 = du_stopsAt_1196
du_stopsAt_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
du_stopsAt_1196 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_1184
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.bf-mono
d_bf'45'mono_1272 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_1272 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.cont-alloc
d_cont'45'alloc_1274 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1274 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2434
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.events
d_events_1276 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_1276 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.frame-pres
d_frame'45'pres_1278 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1278 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.live
d_live_1280 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1280 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.log
d_log_1282 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1282 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.mem-pres
d_mem'45'pres_1284 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_1284 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.no-link
d_no'45'link_1286 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.no-ret
d_no'45'ret_1288 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1288 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.out-mode
d_out'45'mode_1290 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1290 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2432
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.place
d_place_1292 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_1292 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2450
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.returned
d_returned_1294 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_1294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.run
d_run_1296 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_1296 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2436
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.settle
d_settle_1298 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1298 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2430
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.steps
d_steps_1300 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  Integer
d_steps_1300 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2428
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.CalleeRun.stops
d_stops_1302 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_1302 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2442
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.falloc
d_falloc_1338 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1338 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.fclosure
d_fclosure_1340 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1340 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.flink
d_flink_1342 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1342 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.floc
d_floc_1344 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_1344 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.fpc
d_fpc_1346 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1346 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.FlatState.fret
d_fret_1348 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1348 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1384 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1384 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1386 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102
d_value'45'realized_1386 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_2316
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.at-end
d_at'45'end_1448 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1448 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.bf-mono
d_bf'45'mono_1450 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_1450 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2214
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1452 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1452 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.frame-pres
d_frame'45'pres_1454 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1454 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.heap-pres
d_heap'45'pres_1456 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1456 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.live
d_live_1458 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1458 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.log
d_log_1460 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1460 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.no-link
d_no'45'link_1462 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1462 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.no-ret
d_no'45'ret_1464 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1464 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.out-mode
d_out'45'mode_1466 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1466 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2176
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.place
d_place_1468 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_1468 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2196
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.run
d_run_1470 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_1470 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.settle
d_settle_1472 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1472 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2174
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.stack-pres
d_stack'45'pres_1474 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1474 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.steps
d_steps_1476 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer
d_steps_1476 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2172
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Core.ValueRealized.stops
d_stops_1478 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_1478 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2186
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Mach.ApplySetupPres.a16
d_a16_1632 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a16_1632 ~v0 ~v1 = du_a16_1632
du_a16_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a16_1632 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948 v0
      v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Mach.ApplySetupPres.ahl
d_ahl_1650 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_ahl_1650 ~v0 ~v1 = du_ahl_1650
du_ahl_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_ahl_1650 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_ahl_3950 v0
      v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Apply._._+_
d__'43'__1974 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__1974 ~v0 ~v1 = du__'43'__1974
du__'43'__1974 :: Integer -> Integer -> Integer
du__'43'__1974 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.Apply._._≡_
d__'8801'__1990 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.AllocMode
d_AllocMode_2018 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.IR
d_IR_2032 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.List
d_List_2038 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Maybe
d_Maybe_2040 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply._.fst
d_fst_2114 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2114 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.snd
d_snd_2116 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2116 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply._.Nat
d_Nat_2142 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.BeforeFrontier
d_BeforeFrontier_2350 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun
d_CalleeRun_2362 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CellAt
d_CellAt_2368 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.EnvAt
d_EnvAt_2372 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState
d_FlatState_2374 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatSteps
d_FlatSteps_2378 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.IRObsCorrectF
d_IRObsCorrectF_2390 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_2390 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.InputAt
d_InputAt_2394 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.MachineRefinesObsF
d_MachineRefinesObsF_2400 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ResultPlace
d_ResultPlace_2408 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValidAtWF
d_ValidAtWF_2418 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized
d_ValueRealized_2420 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.chain-events
d_chain'45'events_2442 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_chain'45'events_2442 ~v0 ~v1 v2 = du_chain'45'events_2442 v2
du_chain'45'events_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_chain'45'events_2442 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.enter-call
d_enter'45'call_2498 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_2498 ~v0 ~v1 v2 = du_enter'45'call_2498 v2
du_enter'45'call_2498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_2498 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.entry-flat
d_entry'45'flat_2502 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_entry'45'flat_2502 ~v0 ~v1 ~v2 = du_entry'45'flat_2502
du_entry'45'flat_2502 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_entry'45'flat_2502
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_entry'45'flat_1986
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.evalᴰ
d_eval'7472'_2514 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_eval'7472'_2514 ~v0 v1 v2 = du_eval'7472'_2514 v1 v2
du_eval'7472'_2514 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_eval'7472'_2514 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_1156
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.eventsAt
d_eventsAt_2518 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_eventsAt_2518 ~v0 ~v1 v2 = du_eventsAt_2518 v2
du_eventsAt_2518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_eventsAt_2518 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_1168
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.find-thunk
d_find'45'thunk_2598 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_2598 ~v0 ~v1 v2 = du_find'45'thunk_2598 v2
du_find'45'thunk_2598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_2598 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.flat-exec-instr
d_flat'45'exec'45'instr_2622 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_2622 ~v0 ~v1 v2
  = du_flat'45'exec'45'instr_2622 v2
du_flat'45'exec'45'instr_2622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_2622 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.resultAt
d_resultAt_2798 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_resultAt_2798 ~v0 ~v1 v2 = du_resultAt_2798 v2
du_resultAt_2798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_resultAt_2798 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_1176
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.runAt
d_runAt_2802 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runAt_2802 ~v0 ~v1 v2 = du_runAt_2802 v2
du_runAt_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runAt_2802 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_runAt_1160
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.stopsAt
d_stopsAt_2850 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
d_stopsAt_2850 ~v0 ~v1 v2 = du_stopsAt_2850 v2
du_stopsAt_2850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> Bool
du_stopsAt_2850 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_1184
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.bf-mono
d_bf'45'mono_2926 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_2926 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.cont-alloc
d_cont'45'alloc_2928 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_2928 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2434
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.events
d_events_2930 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_2930 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.frame-pres
d_frame'45'pres_2932 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_2932 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.live
d_live_2934 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_2934 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.log
d_log_2936 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_2936 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.mem-pres
d_mem'45'pres_2938 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres_2938 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.no-link
d_no'45'link_2940 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_2940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.no-ret
d_no'45'ret_2942 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_2942 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.out-mode
d_out'45'mode_2944 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_2944 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2432
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.place
d_place_2946 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_2946 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2450
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.returned
d_returned_2948 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returned_2948 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.run
d_run_2950 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_2950 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2436
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.settle
d_settle_2952 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_2952 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2430
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.steps
d_steps_2954 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  Integer
d_steps_2954 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2428
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.CalleeRun.stops
d_stops_2956 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_2956 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2442
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.falloc
d_falloc_2992 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_2992 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.fclosure
d_fclosure_2994 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2994 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.flink
d_flink_2996 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2996 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.floc
d_floc_2998 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_2998 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.fpc
d_fpc_3000 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_3000 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.FlatState.fret
d_fret_3002 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_3002 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.MachineRefinesObsF.traces-agree
d_traces'45'agree_3038 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_3038 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.MachineRefinesObsF.value-realized
d_value'45'realized_3040 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102
d_value'45'realized_3040 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_2316
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.at-end
d_at'45'end_3102 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_3102 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.bf-mono
d_bf'45'mono_3104 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono_3104 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2214
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.cont-alloc
d_cont'45'alloc_3106 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_3106 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2178
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.frame-pres
d_frame'45'pres_3108 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_3108 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.heap-pres
d_heap'45'pres_3110 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_3110 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.live
d_live_3112 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_3112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.log
d_log_3114 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_3114 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.no-link
d_no'45'link_3116 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_3116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.no-ret
d_no'45'ret_3118 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_3118 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.out-mode
d_out'45'mode_3120 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_3120 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2176
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.place
d_place_3122 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_3122 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2196
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.run
d_run_3124 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_3124 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2180
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.settle
d_settle_3126 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_3126 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2174
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.stack-pres
d_stack'45'pres_3128 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_3128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.steps
d_steps_3130 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  Integer
d_steps_3130 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2172
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ValueRealized.stops
d_stops_3132 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_2102 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_3132 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2186
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ApplySetupPres.a16
d_a16_3286 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a16_3286 ~v0 ~v1 v2 = du_a16_3286 v2
du_a16_3286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a16_3286 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ApplySetupPres.ahl
d_ahl_3304 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_ahl_3304 ~v0 ~v1 v2 = du_ahl_3304 v2
du_ahl_3304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_ahl_3304 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_ahl_3950
      (coe v0) v1 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC.call-at
d_call'45'at_3638 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_call'45'at_3638 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC.obs-correct-apply
d_obs'45'correct'45'apply_3666 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_obs'45'correct'45'apply_3666 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10
                               ~v11 ~v12 ~v13 ~v14 v15 v16 v17 v18 ~v19 ~v20 v21 v22
  = du_obs'45'correct'45'apply_3666
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v15 v16 v17 v18 v21 v22
du_obs'45'correct'45'apply_3666 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
du_obs'45'correct'45'apply_3666 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_2346 v15 v16 v17
        -> coe
             du_go_3952 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v14)
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1896
                (coe du_d_3768 (coe v16)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1898
                (coe du_d_3768 (coe v16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.d
d_d_3768 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
d_d_3768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25
  = du_d_3768 v22
du_d_3768 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_PairValidWF_1874
du_d_3768 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1916
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ASP.a16
d_a16_3788 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_a16_3788 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_a16_3788 v2 v5 v8 v16 v17 v18
du_a16_3788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_a16_3788 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.ASP.ahl
d_ahl_3806 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
d_ahl_3806 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_ahl_3806 v2 v5 v8 v16 v17 v18
du_ahl_3806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
du_ahl_3806 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_ahl_3950
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._.go
d_go_3952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_go_3952 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14
          v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 v26 v27
  = du_go_3952
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v15 v16 v17 v18 v25 v26 v27
du_go_3952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
du_go_3952 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v14 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_782 v19 v21 v23 v24
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
               -> case coe v19 of
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v27 v28
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v27
                      -> coe
                           du_assemble_4010 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v6) (coe v7) (coe v8) (coe v26) (coe v10) (coe v11)
                           (coe v12) (coe v13) (coe v27) (coe v21) (coe v24)
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env'45'at_1694
                              (coe du_cvw_3972 (coe v24)))
                           (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.fst-loc
d_fst'45'loc_3970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_3970 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25 ~v26 v27 ~v28 ~v29 ~v30 ~v31 ~v32
  = du_fst'45'loc_3970 v27
du_fst'45'loc_3970 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_fst'45'loc_3970 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.cvw
d_cvw_3972 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
d_cvw_3972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32
  = du_cvw_3972 v31
du_cvw_3972 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ClosureValidWF_1650
du_cvw_3972 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposeClosureWF_1720
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.E
d_E_3974 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
d_E_3974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
         ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32
  = du_E_3974 v31
du_E_3974 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6
du_E_3974 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1684
      (coe du_cvw_3972 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.body
d_body_3976 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_body_3976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32
  = du_body_3976 v31
du_body_3976 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_3976 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body_1686
      (coe du_cvw_3972 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.env
d_env_3978 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  AgdaAny
d_env_3978 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32
  = du_env_3978 v31
du_env_3978 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  AgdaAny
du_env_3978 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_env_1688
      (coe du_cvw_3972 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.blbl
d_blbl_3980 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_blbl_3980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
            ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32
  = du_blbl_3980 v31
du_blbl_3980 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_blbl_3980 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_body'45'label_1690
      (coe du_cvw_3972 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.env-sv-of
d_env'45'sv'45'of_3982 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_env'45'sv'45'of_3982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                       ~v24 ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32 v33
  = du_env'45'sv'45'of_3982 v31 v33
du_env'45'sv'45'of_3982 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_env'45'sv'45'of_3982 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_env'45'at'45'loc_1632 v2 v3 v5 v6
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_env'45'in'45'cell_1636 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
             (coe v2) (coe du_env_3978 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.env-cell-of
d_env'45'cell'45'of_3990 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'cell'45'of_3990 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.arg-sv-of
d_arg'45'sv'45'of_3996 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_arg'45'sv'45'of_3996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                       ~v24 ~v25 ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 v33
  = du_arg'45'sv'45'of_3996 v16 v33
du_arg'45'sv'45'of_3996 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_arg'45'sv'45'of_3996 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_782 v5 v7 v9 v10
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_794 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
             (coe v6) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.arg-cell-of
d_arg'45'cell'45'of_4004 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg'45'cell'45'of_4004 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._.assemble
d_assemble_4010 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
d_assemble_4010 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13
                ~v14 ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 v27 v28
                ~v29 ~v30 v31 ~v32 v33 v34
  = du_assemble_4010
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v16 v17 v18 v19 v26 v27 v28 v31 v33 v34
du_assemble_4010 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_2286
du_assemble_4010 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_2320
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_2216
         (addInt
            (coe (17 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_2428
               (coe
                  du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                  (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_2430
            (coe
               du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_2432
            (coe
               du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)))
         (MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_2434
            (coe
               du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)))
         (coe
            du_run_4192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))
         (\ v19 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_stops_2442
                    (coe
                       du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                       (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))
                    erased))
              erased)
         (\ v19 v20 ->
            coe
              du_place_4212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
              (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18) v19)
         (coe
            du_bf'45'mono'45'apply_4220 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17) (coe v18)))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.callee-env
d_callee'45'env_4134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_callee'45'env_4134 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32 ~v33 ~v34 v35 ~v36
  = du_callee'45'env_4134 v0 v1 v2 v5 v8 v17 v18 v19 v31 v35
du_callee'45'env_4134 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
du_callee'45'env_4134 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_env'45'at'45'loc_1632 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_782
             v11 v10
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_bf'45'advance_4156
                (coe v6) (coe v13))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_carry_4178
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe du_E_3974 (coe v8)) (coe du_env_3978 (coe v8))
                (coe v11) (coe v14))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_env'45'in'45'cell_1636 v10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_794
             v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.callee-arg
d_callee'45'arg_4154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
d_callee'45'arg_4154 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                     ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34 v35 ~v36
  = du_callee'45'arg_4154 v0 v1 v2 v3 v5 v8 v16 v17 v18 v19 v35
du_callee'45'arg_4154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578
du_callee'45'arg_4154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_782 v14 v16 v18 v19
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_782
             v14 v16
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_bf'45'advance_4156
                (coe v8) (coe v18))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_carry_4178
                (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v7) (coe v8)
                (coe v9) (coe v3) (coe v6) (coe v14) (coe v19))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_794 v15
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_794
             v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.callee-in
d_callee'45'in_4170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332
d_callee'45'in_4170 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                    ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29 ~v30 v31 ~v32 v33 v34
  = du_callee'45'in_4170
      v0 v1 v2 v3 v5 v8 v16 v17 v18 v19 v31 v33 v34
du_callee'45'in_4170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332
du_callee'45'in_4170 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_2346
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_ahl_3950
            (coe v2) (coe v4) (coe v5) (coe v7) (coe v8) (coe v9)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_822
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_before'45'ahl'45'suc_4138
            (coe v8))
         (coe
            du_callee'45'env_4134 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
            (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
         (coe
            du_callee'45'arg_4154 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v12)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_before'45'ahl_4134
         (coe v8))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.cinfo
d_cinfo_4172 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cinfo_4172 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
             v27 v28 ~v29 ~v30 v31 ~v32 ~v33 ~v34
  = du_cinfo_4172 v3 v4 v10 v17 v18 v27 v28 v31
du_cinfo_4172 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cinfo_4172 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_closures_2592
      v2
      (MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_EnvType_1684
         (coe du_cvw_3972 (coe v7)))
      v0 v1 (coe du_body_3976 (coe v7)) (coe du_env_3978 (coe v7))
      (coe du_blbl_3980 (coe v7)) v6 v4 (coe du_fst'45'loc_3970 (coe v5))
      v3 v7 erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.j
d_j_4176 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  Integer
d_j_4176 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 v27
         v28 ~v29 ~v30 v31 ~v32 ~v33 ~v34
  = du_j_4176 v3 v4 v10 v17 v18 v27 v28 v31
du_j_4176 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  Integer
du_j_4176 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_cinfo_4172 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.feq
d_feq_4178 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_feq_4178 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.runner
d_runner_4180 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366
d_runner_4180 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
              v27 v28 ~v29 ~v30 v31 ~v32 ~v33 ~v34
  = du_runner_4180 v3 v4 v10 v17 v18 v27 v28 v31
du_runner_4180 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2332 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366
du_runner_4180 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_cinfo_4172 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7)))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.call-eq
d_call'45'eq_4182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_call'45'eq_4182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.crun
d_crun_4184 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366
d_crun_4184 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14
            ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 v27 v28 ~v29
            ~v30 v31 ~v32 v33 v34
  = du_crun_4184
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v16 v17 v18 v19 v26 v27 v28 v31 v33 v34
du_crun_4184 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_CalleeRun_2366
du_crun_4184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16 v17 v18
  = coe
      du_runner_4180 v3 v4 v8 v10 v11 v14 v15 v16
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340
         (coe v2) (coe v6)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
            (coe v2) (coe v5) (coe v7) (coe v10) (coe v11) (coe v12)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
            (coe v2) (coe v5) (coe v7) (coe v10) (coe v11) (coe v12)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe du_env_3978 (coe v16)) (coe v9))
      (addInt
         (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
               (coe v2) (coe v5) (coe v7) (coe v10) (coe v11) (coe v12))))
      v13 (coe MAlonzo.Code.Once.IR.C_Heap_8) erased erased erased erased
      (coe
         du_callee'45'in_4170 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
         (coe v7) (coe v9) (coe v10) (coe v11) (coe v12) (coe v16) (coe v17)
         (coe v18))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.run17
d_run17_4190 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run17_4190 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
             ~v26 ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_run17_4190 v5 v11
du_run17_4190 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_run17_4190 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            v1 (0 :: Integer)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260)
            erased))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
            (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               v1 (1 :: Integer)
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
                  (coe v0))
               erased))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe
                  v1 (2 :: Integer)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
                  erased))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     v1 (3 :: Integer)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
                     erased))
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2308)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe
                        v1 (4 :: Integer)
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2308)
                        erased))
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                        (coe
                           v1 (5 :: Integer)
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
                           erased))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
                           (coe addInt (coe (1 :: Integer)) (coe v0)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              v1 (6 :: Integer)
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
                                 (coe addInt (coe (1 :: Integer)) (coe v0)))
                              erased))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314
                              (coe (2 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                              (coe
                                 v1 (7 :: Integer)
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314
                                    (coe (2 :: Integer)))
                                 erased))
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
                                 (coe addInt (coe (2 :: Integer)) (coe v0)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe
                                    v1 (8 :: Integer)
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264
                                       (coe addInt (coe (2 :: Integer)) (coe v0)))
                                    erased))
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                    (coe
                                       v1 (9 :: Integer)
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
                                       erased))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                       (coe addInt (coe (1 :: Integer)) (coe v0)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                       (coe
                                          v1 (10 :: Integer)
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                             (coe addInt (coe (1 :: Integer)) (coe v0)))
                                          erased))
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          (coe
                                             v1 (11 :: Integer)
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
                                             erased))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                             (coe v0))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             (coe
                                                v1 (12 :: Integer)
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                                   (coe v0))
                                                erased))
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                (coe
                                                   v1 (13 :: Integer)
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
                                                   erased))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                                   (coe addInt (coe (2 :: Integer)) (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased
                                                   (coe
                                                      v1 (14 :: Integer)
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                                                         (coe addInt (coe (2 :: Integer)) (coe v0)))
                                                      erased))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_step'45'at_366
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      erased
                                                      (coe
                                                         v1 (15 :: Integer)
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256)
                                                         erased))
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__352
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased
                                                         (coe
                                                            v1 (16 :: Integer)
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284)
                                                            erased))
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_342)))))))))))))))))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.run
d_run_4192 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_4192 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14
           ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 v27 v28 ~v29
           ~v30 v31 ~v32 v33 v34
  = du_run_4192
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v16 v17 v18 v19 v26 v27 v28 v31 v33 v34
du_run_4192 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
du_run_4192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1170
      (coe du_run17_4190 (coe v5) erased)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_2436
         (coe
            du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.denot-eq
d_denot'45'eq_4194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45'eq_4194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.callFs
d_callFs_4198 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_callFs_4198 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
              ~v27 ~v28 ~v29 ~v30 ~v31 ~v32 ~v33 ~v34
  = du_callFs_4198 v2 v5 v7 v8 v17 v18 v19
du_callFs_4198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_callFs_4198 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
         (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.h-eq
d_h'45'eq_4200 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h'45'eq_4200 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.RE
d_RE_4202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RE_4202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.st-eq
d_st'45'eq_4204 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'eq_4204 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.res-eq
d_res'45'eq_4208 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'eq_4208 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.place
d_place_4212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_4212 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13
             ~v14 ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 v27 v28
             ~v29 ~v30 v31 ~v32 v33 v34 v35 ~v36
  = du_place_4212
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v16 v17 v18 v19 v26 v27 v28 v31 v33 v34
      v35
du_place_4212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
du_place_4212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
              v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_2450
      (coe
         du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))
      v19 erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.bf-mono-apply
d_bf'45'mono'45'apply_4220 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf'45'mono'45'apply_4220 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11
                           ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                           v26 v27 v28 ~v29 ~v30 v31 ~v32 v33 v34 v35 v36 v37
  = du_bf'45'mono'45'apply_4220
      v0 v1 v2 v3 v4 v5 v7 v8 v10 v16 v17 v18 v19 v26 v27 v28 v31 v33 v34
      v35 v36 v37
du_bf'45'mono'45'apply_4220 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
du_bf'45'mono'45'apply_4220 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_2474
      (coe
         du_crun_4184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_a16_3948
            (coe v2) (coe v5) (coe v7) (coe v10) (coe v11) (coe v12)))
      v19 erased v20
      (coe
         MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_788
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v19))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_heapref'45'a16'45''8804'_4148
            (coe v11))
         (coe v20) (coe v21))
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.mem-pres-apply
d_mem'45'pres'45'apply_4230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'apply_4230 = erased
-- Once.CCC.Codegen.IRObsCorrect.Apply.ApplyC._._._.trc
d_trc_4238 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_BlockRuns_2582 ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_EnvAt_1616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trc_4238 = erased
