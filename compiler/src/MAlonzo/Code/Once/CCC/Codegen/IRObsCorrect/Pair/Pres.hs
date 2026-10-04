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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Pair.Pres where

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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
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
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AbstractReg
d_AbstractReg_13 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.⊤
d_'8868'_19 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.BeforeFrontier
d_BeforeFrontier_732 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState
d_FlatState_756 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatSteps
d_FlatSteps_760 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatSteps-++
d_FlatSteps'45''43''43'_762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45''43''43'_762 ~v0 ~v1 ~v2
  = du_FlatSteps'45''43''43'_762
du_FlatSteps'45''43''43'_762 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45''43''43'_762 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized
d_ValueRealized_802 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.chain-events
d_chain'45'events_824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_824 ~v0 ~v1 v2 = du_chain'45'events_824 v2
du_chain'45'events_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_824 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.falloc
d_falloc_1370 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_1370 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.fclosure
d_fclosure_1372 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1372 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.flink
d_flink_1374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1374 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.floc
d_floc_1376 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_1376 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.fpc
d_fpc_1378 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1378 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.FlatState.fret
d_fret_1380 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1380 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.at-end
d_at'45'end_1480 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.bf-mono
d_bf'45'mono_1482 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_1482 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1484 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_1484 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.frame-pres
d_frame'45'pres_1486 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.heap-pres
d_heap'45'pres_1488 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.live
d_live_1490 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.log
d_log_1492 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.no-link
d_no'45'link_1494 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.no-ret
d_no'45'ret_1496 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.out-mode
d_out'45'mode_1498 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1498 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.place
d_place_1500 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1500 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.run
d_run_1502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.settle
d_settle_1504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1504 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.stack-pres
d_stack'45'pres_1506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.steps
d_steps_1508 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_1508 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Core.ValueRealized.stops
d_stops_1510 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1514 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.cf-u3
d_cf'45'u3_1830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_1830 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.fresh
d_fresh_1832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_1832 ~v0 ~v1 = du_fresh_1832
du_fresh_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_1832 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_fresh_5148 v6
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.heapref-u2
d_heapref'45'u2_1834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_1834 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.hl
d_hl_1836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_1836 ~v0 ~v1 = du_hl_1836
du_hl_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_1836 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_hl_5144 v0 v1
      v4
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.mem-pres-from
d_mem'45'pres'45'from_1838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_1838 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u10
d_u10_1840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_1840 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u10_1840 v2 v3 v4 v5 v6
du_u10_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_1840 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u10_5104
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u2
d_u2_1842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_1842 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u2_1842 v2 v3 v6
du_u2_1842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_1842 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u2_5088
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u3
d_u3_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_1844 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u3_1844 v2 v3 v6
du_u3_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_1844 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u3_5090
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u4
d_u4_1846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_1846 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u4_1846 v2 v3 v6
du_u4_1846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_1846 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u4_5092
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u5
d_u5_1848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_1848 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u5_1848 v2 v3 v6
du_u5_1848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_1848 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u5_5094
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u6
d_u6_1850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_1850 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u6_1850 v2 v3 v4 v6
du_u6_1850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_1850 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u6_5096
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u7
d_u7_1852 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_1852 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u7_1852 v2 v3 v4 v6
du_u7_1852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_1852 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u7_5098
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u8
d_u8_1854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_1854 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u8_1854 v2 v3 v4 v5 v6
du_u8_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_1854 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u8_5100
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Mach.NineStepPres.u9
d_u9_1856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_1856 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u9_1856 v2 v3 v4 v5 v6
du_u9_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_1856 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u9_5102
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._._++_
d__'43''43'__1950 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__1950 ~v0 ~v1 = du__'43''43'__1950
du__'43''43'__1950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__1950 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.List.Base.du__'43''43'__32 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._._≡_
d__'8801'__1966 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._._≤_
d__'8804'__1970 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AbstractInstr
d_AbstractInstr_1992 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AbstractTrace
d_AbstractTrace_1994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> ()
d_AbstractTrace_1994 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState
d_AllocState_2000 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics
d_FrameSemantics_2028 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.HeapLocation
d_HeapLocation_2036 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.IR
d_IR_2044 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.IRTy
d_IRTy_2046 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.List
d_List_2058 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState
d_LocState_2060 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Maybe
d_Maybe_2064 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.StoredValue
d_StoredValue_2092 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.ValueLocation
d_ValueLocation_2100 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.readReg
d_readReg_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_2222 ~v0 ~v1 = du_readReg_2222
du_readReg_2222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_2222 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.sv-as-loc
d_sv'45'as'45'loc_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_2252 ~v0 ~v1 = du_sv'45'as'45'loc_2252
du_sv'45'as'45'loc_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_2252 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370 v1
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.Nat
d_Nat_2280 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_2304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_2304 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.block-size
d_block'45'size_2518 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Integer
d_block'45'size_2518 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.current-frame
d_current'45'frame_2520 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> AgdaAny
d_current'45'frame_2520 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.frame-slots
d_frame'45'slots_2522 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_frame'45'slots_2522 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.next-heap-ref
d_next'45'heap'45'ref_2524 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'heap'45'ref_2524 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.next-slot
d_next'45'slot_2526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
d_next'45'slot_2526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_590 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.AllocState.saved-frames
d_saved'45'frames_2528 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_2528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics._≟F_
d__'8799'F__3028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__3028 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics._≺_
d__'8826'__3030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__3030 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.Frame
d_Frame_3032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_3032 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.float-format
d_float'45'format_3034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_3034 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.frame-base
d_frame'45'base_3036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_3036 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_3038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_3038 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.frame-word
d_frame'45'word_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_3040 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_3042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_3042 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.fs-interp
d_fs'45'interp_3044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_3044 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.shift-base
d_shift'45'base_3046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_3046 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.shift-frame
d_shift'45'frame_3048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_3048 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.slot-addr
d_slot'45'addr_3050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_3050 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_3052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_3052 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.slot-injective
d_slot'45'injective_3054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_3054 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_3056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_3056 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.≺-compare
d_'8826''45'compare_3058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_3058 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_3060 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.FrameSemantics.≺-trans
d_'8826''45'trans_3062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_3062 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.HeapLocation.heap-offset
d_heap'45'offset_3136 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_heap'45'offset_3136 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.HeapLocation.heap-ref
d_heap'45'ref_3138 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_heap'45'ref_3138 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState.ev-log
d_ev'45'log_3264 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_3264 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState.halted
d_halted_3266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_halted_3266 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_422 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState.heapMem
d_heapMem_3268 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_heapMem_3268 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState.regs
d_regs_3270 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs_3270 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.LocState.stackMem
d_stackMem_3272 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_stackMem_3272 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres._.MemOps.readLoc
d_readLoc_3290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_3290 ~v0 ~v1 = du_readLoc_3290
du_readLoc_3290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_3290 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.BeforeFrontier
d_BeforeFrontier_3796 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState
d_FlatState_3820 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatSteps
d_FlatSteps_3824 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatSteps-++
d_FlatSteps'45''43''43'_3826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_FlatSteps'45''43''43'_3826 ~v0 ~v1 ~v2
  = du_FlatSteps'45''43''43'_3826
du_FlatSteps'45''43''43'_3826 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_FlatSteps'45''43''43'_3826 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      v6 v7
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized
d_ValueRealized_3866 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.chain-events
d_chain'45'events_3888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_chain'45'events_3888 ~v0 ~v1 v2 = du_chain'45'events_3888 v2
du_chain'45'events_3888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_chain'45'events_3888 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_604
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.falloc
d_falloc_4434 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_4434 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.fclosure
d_fclosure_4436 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_4436 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.flink
d_flink_4438 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_4438 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.floc
d_floc_4440 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_4440 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.fpc
d_fpc_4442 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_4442 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.FlatState.fret
d_fret_4444 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_4444 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.at-end
d_at'45'end_4544 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4544 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.bf-mono
d_bf'45'mono_4546 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_4546 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.cont-alloc
d_cont'45'alloc_4548 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_4548 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.frame-pres
d_frame'45'pres_4550 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4550 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.heap-pres
d_heap'45'pres_4552 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4552 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.live
d_live_4554 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4554 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.log
d_log_4556 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4556 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.no-link
d_no'45'link_4558 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4558 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.no-ret
d_no'45'ret_4560 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4560 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.out-mode
d_out'45'mode_4562 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4562 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.place
d_place_4564 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4564 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.run
d_run_4566 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4566 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.settle
d_settle_4568 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4568 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.stack-pres
d_stack'45'pres_4570 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4570 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.steps
d_steps_4572 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_4572 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.ValueRealized.stops
d_stops_4574 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4574 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4578 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.cf-u3
d_cf'45'u3_4894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_4894 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.fresh
d_fresh_4896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_4896 ~v0 ~v1 ~v2 = du_fresh_4896
du_fresh_4896 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_4896 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_fresh_5148 v5
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.heapref-u2
d_heapref'45'u2_4898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_4898 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.hl
d_hl_4900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_4900 ~v0 ~v1 v2 = du_hl_4900 v2
du_hl_4900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_4900 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_hl_5144
      (coe v0) v1 v4
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.mem-pres-from
d_mem'45'pres'45'from_4902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_4902 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u10
d_u10_4904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_4904 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u10_4904 v2 v3 v4 v5 v6
du_u10_4904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_4904 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u10_5104
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u2
d_u2_4906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_4906 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u2_4906 v2 v3 v6
du_u2_4906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_4906 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u2_5088
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u3
d_u3_4908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_4908 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u3_4908 v2 v3 v6
du_u3_4908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_4908 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u3_5090
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u4
d_u4_4910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_4910 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u4_4910 v2 v3 v6
du_u4_4910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_4910 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u4_5092
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u5
d_u5_4912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_4912 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u5_4912 v2 v3 v6
du_u5_4912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_4912 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u5_5094
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u6
d_u6_4914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_4914 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u6_4914 v2 v3 v4 v6
du_u6_4914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_4914 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u6_5096
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u7
d_u7_4916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_4916 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u7_4916 v2 v3 v4 v6
du_u7_4916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_4916 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u7_5098
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u8
d_u8_4918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_4918 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u8_4918 v2 v3 v4 v5 v6
du_u8_4918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_4918 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u8_5100
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC._.NineStepPres.u9
d_u9_4920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_4920 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_u9_4920 v2 v3 v4 v5 v6
du_u9_4920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_4920 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u9_5102
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.pair-p1
d_pair'45'p1_5026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_pair'45'p1_5026 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8
  = du_pair'45'p1_5026 v2 v4 v6 v7 v8
du_pair'45'p1_5026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_pair'45'p1_5026 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.pair-p2
d_pair'45'p2_5028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_pair'45'p2_5028 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_pair'45'p2_5028 v2 v4 v5 v6 v7 v8
du_pair'45'p2_5028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_pair'45'p2_5028 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
         (coe v2))
      (coe
         du_pair'45'p1_5026 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.pair-m1
d_pair'45'm1_5054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_pair'45'm1_5054 ~v0 ~v1 v2 ~v3 v4 v5
  = du_pair'45'm1_5054 v2 v4 v5
du_pair'45'm1_5054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_pair'45'm1_5054 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.pair-m2
d_pair'45'm2_5056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_pair'45'm2_5056 ~v0 ~v1 v2 ~v3 v4 v5
  = du_pair'45'm2_5056 v2 v4 v5
du_pair'45'm2_5056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_pair'45'm2_5056 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258
         (coe v1))
      (coe du_pair'45'm1_5054 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.at-end
d_at'45'end_5120 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_5120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.bf-mono
d_bf'45'mono_5122 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono_5122 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.cont-alloc
d_cont'45'alloc_5124 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_cont'45'alloc_5124 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.frame-pres
d_frame'45'pres_5126 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_5126 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.heap-pres
d_heap'45'pres_5128 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_5128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.live
d_live_5130 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_5130 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.log
d_log_5132 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_5132 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.no-link
d_no'45'link_5134 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_5134 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.no-ret
d_no'45'ret_5136 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_5136 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.out-mode
d_out'45'mode_5138 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_5138 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.place
d_place_5140 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5140 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3694
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.run
d_run_5142 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_5142 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.settle
d_settle_5144 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_5144 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.stack-pres
d_stack'45'pres_5146 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_5146 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.steps
d_steps_5148 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_steps_5148 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3670
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.VR.stops
d_stops_5150 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_5150 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.backup
d_backup_5152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_backup_5152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_backup_5152 v8
du_backup_5152 :: Integer -> Integer
du_backup_5152 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.fst-stash
d_fst'45'stash_5154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_fst'45'stash_5154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                    ~v24 ~v25
  = du_fst'45'stash_5154 v8
du_fst'45'stash_5154 :: Integer -> Integer
du_fst'45'stash_5154 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.snd-stash
d_snd'45'stash_5156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_snd'45'stash_5156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                    ~v24 ~v25
  = du_snd'45'stash_5156 v8
du_snd'45'stash_5156 :: Integer -> Integer
du_snd'45'stash_5156 v0 = coe addInt (coe (2 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.pair-stash
d_pair'45'stash_5158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_pair'45'stash_5158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                     ~v24 ~v25
  = du_pair'45'stash_5158 v8
du_pair'45'stash_5158 :: Integer -> Integer
du_pair'45'stash_5158 v0 = coe addInt (coe (3 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.f-start
d_f'45'start_5160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer
d_f'45'start_5160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  ~v25
  = du_f'45'start_5160 v8
du_f'45'start_5160 :: Integer -> Integer
du_f'45'start_5160 v0 = coe addInt (coe (4 :: Integer)) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.p1
d_p1_5162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_p1_5162 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13
          v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_p1_5162 v2 v11 v12 v13 v14
du_p1_5162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_p1_5162 v0 v1 v2 v3 v4
  = coe
      du_pair'45'p1_5026 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.p2
d_p2_5164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_p2_5164 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12 v13
          v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_p2_5164 v2 v8 v11 v12 v13 v14
du_p2_5164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_p2_5164 v0 v1 v2 v3 v4 v5
  = coe
      du_pair'45'p2_5028 (coe v0) (coe v2) (coe v1) (coe v3) (coe v4)
      (coe v5)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.fsF
d_fsF_5166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fsF_5166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_fsF_5166 v16
du_fsF_5166 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fsF_5166 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.m1
d_m1_5168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_m1_5168 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_m1_5168 v2 v8 v18
du_m1_5168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_m1_5168 v0 v1 v2
  = coe
      du_pair'45'm1_5054 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.m2
d_m2_5170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_m2_5170 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_m2_5170 v2 v8 v18
du_m2_5170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_m2_5170 v0 v1 v2
  = coe
      du_pair'45'm2_5056 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.gs
d_gs_5172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_gs_5172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_gs_5172 v23
du_gs_5172 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_gs_5172 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.tail-alloc
d_tail'45'alloc_5174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_tail'45'alloc_5174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                     ~v24 v25
  = du_tail'45'alloc_5174 v8 v25
du_tail'45'alloc_5174 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_tail'45'alloc_5174 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_596
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
               (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
               (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
               (coe v1))))
      (coe du_snd'45'stash_5156 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
               (coe v1))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
               (coe v1))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.cf-u3
d_cf'45'u3_5178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'u3_5178 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.fresh
d_fresh_5180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh_5180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_fresh_5180 v8 v25
du_fresh_5180 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh_5180 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_fresh_5148
      (coe du_tail'45'alloc_5174 (coe v0) (coe v1))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.heapref-u2
d_heapref'45'u2_5182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'u2_5182 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.hl
d_hl_5184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl_5184 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_hl_5184 v2 v8 v25
du_hl_5184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_hl_5184 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_hl_5144
      (coe v0) (coe addInt (coe (2 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.mem-pres-from
d_mem'45'pres'45'from_5186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'from_5186 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u10
d_u10_5188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u10_5188 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u10_5188 v2 v8 v25
du_u10_5188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u10_5188 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                 (coe addInt (coe (1 :: Integer)) (coe v1)) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                    (coe addInt (coe (2 :: Integer)) (coe v1)) in
          coe
            (let v6
                   = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u10_5104
                  (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u2
d_u2_5190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u2_5190 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u2_5190 v2 v8 v25
du_u2_5190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u2_5190 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u2_5088
            (coe v0) (coe v3) (coe v4)))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u3
d_u3_5192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u3_5192 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u3_5192 v2 v8 v25
du_u3_5192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u3_5192 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u3_5090
            (coe v0) (coe v3) (coe v4)))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u4
d_u4_5194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u4_5194 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u4_5194 v2 v8 v25
du_u4_5194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u4_5194 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u4_5092
            (coe v0) (coe v3) (coe v4)))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u5
d_u5_5196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u5_5196 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u5_5196 v2 v8 v25
du_u5_5196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u5_5196 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u5_5094
            (coe v0) (coe v3) (coe v4)))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u6
d_u6_5198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u6_5198 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u6_5198 v2 v8 v25
du_u6_5198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u6_5198 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                 (coe addInt (coe (1 :: Integer)) (coe v1)) in
       coe
         (let v5
                = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u6_5096
               (coe v0) (coe v3) (coe v4) (coe v5))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u7
d_u7_5200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u7_5200 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u7_5200 v2 v8 v25
du_u7_5200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u7_5200 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                 (coe addInt (coe (1 :: Integer)) (coe v1)) in
       coe
         (let v5
                = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u7_5098
               (coe v0) (coe v3) (coe v4) (coe v5))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u8
d_u8_5202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u8_5202 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u8_5202 v2 v8 v25
du_u8_5202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u8_5202 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                 (coe addInt (coe (1 :: Integer)) (coe v1)) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                    (coe addInt (coe (2 :: Integer)) (coe v1)) in
          coe
            (let v6
                   = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u8_5100
                  (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.NSP.u9
d_u9_5204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_u9_5204 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_u9_5204 v2 v8 v25
du_u9_5204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_u9_5204 v0 v1 v2
  = let v3 = addInt (coe (2 :: Integer)) (coe v1) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                 (coe addInt (coe (1 :: Integer)) (coe v1)) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
                    (coe addInt (coe (2 :: Integer)) (coe v1)) in
          coe
            (let v6
                   = MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u9_5102
                  (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.settle
d_settle_5206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_5206 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_settle_5206 v2 v8 v25
du_settle_5206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_settle_5206 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u10_5104
      (coe v0) (coe addInt (coe (2 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
         (coe addInt (coe (1 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
         (coe addInt (coe (2 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.pair-hl
d_pair'45'hl_5208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_pair'45'hl_5208 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  v25
  = du_pair'45'hl_5208 v2 v8 v25
du_pair'45'hl_5208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_pair'45'hl_5208 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_hl_5144
      (coe v0) (coe addInt (coe (2 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
         (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.cf-tail
d_cf'45'tail_5210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'tail_5210 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.heapref-tail
d_heapref'45'tail_5212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'tail_5212 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.heapref-gs≤
d_heapref'45'gs'8804'_5214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heapref'45'gs'8804'_5214 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                           ~v23 ~v24 v25
  = du_heapref'45'gs'8804'_5214 v2 v8 v25
du_heapref'45'gs'8804'_5214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heapref'45'gs'8804'_5214 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                  (coe v2)))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
               (coe
                  MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u2_5088
                     (coe v0) (coe addInt (coe (2 :: Integer)) (coe v1))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                        (coe v2))))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Machine.du_u2_5088
                        (coe v0) (coe addInt (coe (2 :: Integer)) (coe v1))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                           (coe v2))))))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.cf-mid
d_cf'45'mid_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'mid_5216 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.heapref-mid
d_heapref'45'mid_5218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heapref'45'mid_5218 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.n≤f-start
d_n'8804'f'45'start_5220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'f'45'start_5220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                         ~v23 ~v24 ~v25
  = du_n'8804'f'45'start_5220 v8
du_n'8804'f'45'start_5220 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'f'45'start_5220 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe addInt (coe (1 :: Integer)) (coe v0)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
               (coe addInt (coe (2 :: Integer)) (coe v0)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
               (coe addInt (coe (3 :: Integer)) (coe v0)))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-f
d_bf'45'f_5224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'f_5224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
               ~v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
               ~v25
  = du_bf'45'f_5224 v8 v13
du_bf'45'f_5224 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'f_5224 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe du_n'8804'f'45'start_5220 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe v1)))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-after-f
d_bf'45'after'45'f_5230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'after'45'f_5230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        ~v23
  = du_bf'45'after'45'f_5230 v16
du_bf'45'after'45'f_5230 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'after'45'f_5230 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-mid
d_bf'45'mid_5236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mid_5236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                 ~v25 v26
  = du_bf'45'mid_5236 v18 v26
du_bf'45'mid_5236 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'mid_5236 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                  (coe v0)))))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-after-g
d_bf'45'after'45'g_5244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'after'45'g_5244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
                        v23
  = du_bf'45'after'45'g_5244 v23
du_bf'45'after'45'g_5244 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'after'45'g_5244 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-to-m2
d_bf'45'to'45'm2_5250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'to'45'm2_5250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23
                      ~v24 ~v25 v26 v27 v28
  = du_bf'45'to'45'm2_5250 v18 v26 v27 v28
du_bf'45'to'45'm2_5250 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'to'45'm2_5250 v0 v1 v2 v3
  = coe
      du_bf'45'mid_5236 v0 v1 v2
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
         v0 v1 v2 v3)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-to-gs
d_bf'45'to'45'gs_5262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'to'45'gs_5262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23
                      ~v24 v25 v26 v27 v28
  = du_bf'45'to'45'gs_5262 v18 v25 v26 v27 v28
du_bf'45'to'45'gs_5262 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'to'45'gs_5262 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_bf'45'mono_3712
      v1 v2 v3
      (coe du_bf'45'to'45'm2_5250 (coe v0) (coe v2) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-tail
d_bf'45'tail_5274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'tail_5274 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
                  v25 v26
  = du_bf'45'tail_5274 v2 v8 v25 v26
du_bf'45'tail_5274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'tail_5274 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v3))
      (coe du_heapref'45'gs'8804'_5214 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.frame-pres-pair
d_frame'45'pres'45'pair_5278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres'45'pair_5278 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.bf-mono-pair
d_bf'45'mono'45'pair_5284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_bf'45'mono'45'pair_5284 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22
                          ~v23 ~v24 v25 v26 v27 v28
  = du_bf'45'mono'45'pair_5284 v2 v8 v18 v25 v26 v27 v28
du_bf'45'mono'45'pair_5284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_bf'45'mono'45'pair_5284 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_bf'45'tail_5274 v0 v1 v3 v4 v5
      (coe
         du_bf'45'to'45'gs_5262 (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.mem-pres-to-fsF
d_mem'45'pres'45'to'45'fsF_5294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'to'45'fsF_5294 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.w-g-outer
d_w'45'g'45'outer_5302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_w'45'g'45'outer_5302 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
                       ~v25 v26 v27
  = du_w'45'g'45'outer_5302 v2 v8 v18 v21 v26 v27
du_w'45'g'45'outer_5302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_w'45'g'45'outer_5302 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe du_m2_5170 (coe v0) (coe v1) (coe v2)))))
      (coe v4)
      (coe du_bf'45'to'45'm2_5250 (coe v2) (coe v1) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.mem-pres-to-gs
d_mem'45'pres'45'to'45'gs_5310 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'to'45'gs_5310 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.frame-pres-to-gs
d_frame'45'pres'45'to'45'gs_5316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres'45'to'45'gs_5316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.Fill.w-gs
d_w'45'gs_5326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_w'45'gs_5326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
               ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
               ~v26 ~v27 v28 v29
  = du_w'45'gs_5326 v8 v18 v25 v28 v29
du_w'45'gs_5326 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_w'45'gs_5326 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v0))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe addInt (coe (1 :: Integer)) (coe v0))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3672
                  (coe v2)))))
      (coe v3)
      (coe
         du_bf'45'to'45'gs_5262 (coe v1) (coe v2) (coe v0) (coe v3)
         (coe v4))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.Fill.w-g
d_w'45'g_5334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_w'45'g_5334 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
              ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25 ~v26
              ~v27 v28 v29
  = du_w'45'g_5334 v2 v8 v18 v21 v28 v29
du_w'45'g_5334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_w'45'g_5334 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
            (coe
               MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
               (coe du_m2_5170 (coe v0) (coe v1) (coe v2)))))
      (coe v4)
      (coe du_bf'45'to'45'm2_5250 (coe v2) (coe v1) (coe v4) (coe v5))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.Fill.mem-pres-pair
d_mem'45'pres'45'pair_5342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'pres'45'pair_5342 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.Fill.stack-pres-pair
d_stack'45'pres'45'pair_5352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres'45'pair_5352 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairPres.Fill.heap-pres-pair
d_heap'45'pres'45'pair_5360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres'45'pair_5360 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace.pair-chain-events
d_pair'45'chain'45'events_5400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'chain'45'events_5400 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.after-g
d_after'45'g_5422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_after'45'g_5422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 ~v21 ~v22
  = du_after'45'g_5422 v17 v19
du_after'45'g_5422 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_after'45'g_5422 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      (coe v0) (coe v1)
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.ev-after-g
d_ev'45'after'45'g_5424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'after'45'g_5424 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.after-f
d_after'45'f_5428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_after'45'f_5428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 v16 v17 ~v18 v19 ~v20 ~v21 ~v22
  = du_after'45'f_5428 v16 v17 v19
du_after'45'f_5428 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_after'45'f_5428 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      (coe v0) (coe du_after'45'g_5422 (coe v1) (coe v2))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.ev-after-f
d_ev'45'after'45'f_5430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'after'45'f_5430 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.after-pre
d_after'45'pre_5434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_after'45'pre_5434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 v19 ~v20 ~v21 ~v22
  = du_after'45'pre_5434 v15 v16 v17 v19
du_after'45'pre_5434 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
du_after'45'pre_5434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_1192
      (coe v0) (coe du_after'45'f_5428 (coe v1) (coe v2) (coe v3))
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace._.ev-after-pre
d_ev'45'after'45'pre_5436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45'after'45'pre_5436 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace.pair-chain-events-g
d_pair'45'chain'45'events'45'g_5470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'chain'45'events'45'g_5470 = erased
-- Once.CCC.Codegen.IRObsCorrect.Pair.Pres.PairPresC.PairTrace.pair-chain-events-f
d_pair'45'chain'45'events'45'f_5506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'chain'45'events'45'f_5506 = erased
