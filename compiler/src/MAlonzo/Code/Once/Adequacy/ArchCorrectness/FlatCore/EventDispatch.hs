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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockStep
d_BlockStep_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_BlockStep_34 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr
d_CompiledCorr_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv
d_FlatInv_50 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Reachable
d_Reachable_56 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt
d_RunAt_58 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply
d_Supply_68 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.blk-len
d_blk'45'len_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
d_blk'45'len_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'len_76 v8
du_blk'45'len_76 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
du_blk'45'len_76 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView
d_HeapView_382 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slots
d_slots_652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_slots_652 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_slots_652 v2
du_slots_652 :: Integer -> Integer -> Integer
du_slots_652 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.HDom
d_HDom_760 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_760 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.caddr
d_caddr_762 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_762 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.dom-below
d_dom'45'below_764 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_764 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_510
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.front-lo
d_front'45'lo_766 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_766 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr
d_haddr_768 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_768 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_490
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-inj
d_haddr'45'inj_770 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_770 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-suc
d_haddr'45'suc_772 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_772 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.hfront
d_hfront_774 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer
d_hfront_774 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.lo
d_lo_776 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer
d_lo_776 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.code-eq
d_code'45'eq_824 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_824 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.dataCorr
d_dataCorr_826 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1082
d_dataCorr_826 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.pc-off
d_pc'45'off_828 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_828 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.ret-eq
d_ret'45'eq_830 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  AgdaAny
d_ret'45'eq_830 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_658
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-closure
d_inv'45'closure_834 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  AgdaAny
d_inv'45'closure_834 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1058
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-env
d_inv'45'env_836 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  AgdaAny
d_inv'45'env_836 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1064
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-ev
d_inv'45'ev_838 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_838 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-regtag
d_inv'45'regtag_840 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522
d_inv'45'regtag_840 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1060
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-run
d_inv'45'run_842 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416
d_inv'45'run_842 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-started
d_inv'45'started_844 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_inv'45'started_844 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-wf
d_inv'45'wf_846 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734
d_inv'45'wf_846 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.ArithEnv
d_ArithEnv_854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_ArithEnv_854 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.EvExtractor
d_EvExtractor_856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_EvExtractor_856 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events
d_run'45'events_858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events_858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'events_858 v8 v9 v10
du_run'45'events_858 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events_858 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-emit
d_run'45'emit_900 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_900 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-ir
d_run'45'ir_902 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_902 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_434
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-linked
d_run'45'linked_904 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_904 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_438
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-reach
d_run'45'reach_906 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_358
d_run'45'reach_906 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-tbl
d_run'45'tbl_908 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_908 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_432
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.arith-sigop-contract
d_arith'45'sigop'45'contract_924 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arith'45'sigop'45'contract_924 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_1980
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.bss
d_bss_926 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_846
d_bss_926 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.call-room
d_call'45'room_928 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_call'45'room_928 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.count-no-wrap
d_count'45'no'45'wrap_930 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_930 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1914
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.external-sigop-contract
d_external'45'sigop'45'contract_932 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_external'45'sigop'45'contract_932 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_2000
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.float-fits
d_float'45'fits_934 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_934 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_1950
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.heap-room
d_heap'45'room_936 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'room_936 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1844
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lit-fits
d_lit'45'fits_938 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_938 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_1938
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lo-fits
d_lo'45'fits_940 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_940 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_1960
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.reg-range
d_reg'45'range_942 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reg'45'range_942 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.ret-no-wrap
d_ret'45'no'45'wrap_944 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_944 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1904
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.scratch-dec-guarded
d_scratch'45'dec'45'guarded_946 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'dec'45'guarded_946 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1892
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.stack-room
d_stack'45'room_948 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'room_948 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1858
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.sts
d_sts_950 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1444
d_sts_950 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.tag-fits
d_tag'45'fits_952 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_952 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_1926
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.compile-trace
d_compile'45'trace_960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [AgdaAny]
d_compile'45'trace_960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_compile'45'trace_960 v8
du_compile'45'trace_960 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [AgdaAny]
du_compile'45'trace_960 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'trace_108
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.memory
d_memory_1014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> Integer -> Maybe Integer
d_memory_1014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_memory_1014 v9
du_memory_1014 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Integer -> Maybe Integer
du_memory_1014 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_memory_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.rreg
d_rreg_1018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> AgdaAny -> Integer
d_rreg_1018 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_rreg_1018 v9
du_rreg_1018 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> AgdaAny -> Integer
du_rreg_1018 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.in1-reg
d_in1'45'reg_1048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_in1'45'reg_1048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_in1'45'reg_1048 v6
du_in1'45'reg_1048 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_in1'45'reg_1048 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_44
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sp-reg
d_sp'45'reg_1054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_sp'45'reg_1054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_sp'45'reg_1054 v6
du_sp'45'reg_1054 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_sp'45'reg_1054 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.enter-call
d_enter'45'call_1064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_enter'45'call_1064 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enter'45'call_1064 v1
du_enter'45'call_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_1064 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch
d_fetch_1070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_1070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_fetch_1070
du_fetch_1070 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_1070 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-fn
d_find'45'fn_1072 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
d_find'45'fn_1072 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'fn_1072 v1
du_find'45'fn_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Maybe Integer
du_find'45'fn_1072 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-thunk
d_find'45'thunk_1074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_1074 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'thunk_1074 v1
du_find'45'thunk_1074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_1074 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-exec-instr
d_flat'45'exec'45'instr_1076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1076 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_flat'45'exec'45'instr_1076 v1
du_flat'45'exec'45'instr_1076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1076 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label
d_find'45'label_1078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_1078 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'label_1078 v1
du_find'45'label_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_1078 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.readLoc
d_readLoc_1088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readLoc_1088
du_readLoc_1088 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1088
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatWF
d_FlatWF_1094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_1094 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sv-below
d_sv'45'below_1100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_1100 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatRegTag
d_FlatRegTag_1114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_1114 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Frame
d_Frame_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Frame_1130 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RetMatch
d_RetMatch_1140 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.event-of
d_event'45'of_1324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_event'45'of_1324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_event'45'of_1324
du_event'45'of_1324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_event'45'of_1324
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_458
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events
d_flat'45'events_1326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events_1326 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_flat'45'events_1326 v1
du_flat'45'events_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events_1326 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-fetch
d_flat'45'events'45'fetch_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events'45'fetch_1328 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_flat'45'events'45'fetch_1328 v1
du_flat'45'events'45'fetch_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events'45'fetch_1328 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_468
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-step
d_flat'45'events'45'step_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events'45'step_1330 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_flat'45'events'45'step_1330 v1
du_flat'45'events'45'step_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events'45'step_1330 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_466
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.call≢thunk
d_call'8802'thunk_1336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'8802'thunk_1336 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.callfn≢thunk
d_callfn'8802'thunk_1344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_callfn'8802'thunk_1344 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.ret≢thunk
d_ret'8802'thunk_1352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ret'8802'thunk_1352 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.EventsIH
d_EventsIH_1426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  Integer -> ()
d_EventsIH_1426 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ccc-step-bs
d_ccc'45'step'45'bs_1462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccc'45'step'45'bs_1462 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                         ~v11 v12 ~v13 v14 v15 v16 v17 v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25
                         ~v26 ~v27
  = du_ccc'45'step'45'bs_1462
      v1 v8 v12 v14 v15 v16 v17 v18 v20 v21 v22
du_ccc'45'step'45'bs_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccc'45'step'45'bs_1462 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
               (coe v1))
            (coe v8))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_1498 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe v10))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_1498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1498 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 v14 v15 v16 v17 v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26 ~v27
  = du_rec_1498 v1 v12 v14 v15 v16 v17 v18 v20 v21 v22
du_rec_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_1498 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      v2 v1 v3 v4 v5
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v0
         v7 v5 v6)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1082
         (coe v0) (coe v7) (coe v5) (coe v6) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.result
d_result_1500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_1500 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.log≡
d_log'8801'_1502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_1502 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.thunk-step
d_thunk'45'step_1530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'step_1530 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12
                     ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_thunk'45'step_1530
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_thunk'45'step_1530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'step_1530 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17
  = coe
      du_ccc'45'step'45'bs_1462 (coe v1) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1628
         (coe v7)
         (coe
            du_lo''_1574 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_front'45'lo''_1580 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17)))
      (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 (coe v14)
            (coe v15)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1926
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
            (coe v6))
         v7 v11 v12 v13 v14 v15
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_lnk_1564 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
               (coe v14) (coe v15) (coe v17)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_pend_1566 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
               (coe v14) (coe v15) (coe v17)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_pend_1566 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
                  (coe v14) (coe v15) (coe v17))))
         v16 erased erased
         (coe
            du_lo''_1574 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_lo'''8804'lo_1576 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_front'45'lo''_1580 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17))
         (coe
            du_lo'''8804'rsp_1578 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_fits_1570 (coe v2) (coe v6) (coe v7) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17))
         erased
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
            v6 v7 v11 v12 v13
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v3))
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
               (coe v17))
            v16)
         erased erased)
      (coe v17)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lnk
d_lnk_1564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lnk_1564 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 ~v16 v17 v18 ~v19 v20 v21 ~v22 v23 ~v24 ~v25
  = du_lnk_1564 v0 v1 v2 v17 v18 v20 v21 v23
du_lnk_1564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lnk_1564 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'link_2390
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.pend
d_pend_1566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pend_1566 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 v20 v21 ~v22 v23 ~v24 ~v25
  = du_pend_1566 v0 v1 v2 v17 v18 v20 v21 v23
du_pend_1566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pend_1566 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'ret_2416
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.room
d_room_1568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25
  = du_room_1568 v11 v12 v17 v18 v19 v20 v21 v22 v23 v25
du_room_1568 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1568 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1858
      v0 v1 v2 v3 v4 v6
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v8))
      v7
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v9)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.fits
d_fits_1570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1570 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_fits_1570 v2 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_fits_1570 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v7)))
      (coe
         du_room_1568 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-rsp
d_front'45'rsp_1572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_front'45'rsp_1572 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_front'45'rsp_1572 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1572 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v1))
      (coe
         du_room_1568 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'
d_lo''_1574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1574 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo''_1574 v2 v6 v9 v12 v19 v21
du_lo''_1574 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> Integer
du_lo''_1574 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤lo
d_lo'''8804'lo_1576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1576 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo'''8804'lo_1576 v2 v6 v9 v12 v19 v21
du_lo'''8804'lo_1576 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1576 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤rsp
d_lo'''8804'rsp_1578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1578 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo'''8804'rsp_1578 v2 v6 v9 v12 v19 v21
du_lo'''8804'rsp_1578 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1578 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-lo'
d_front'45'lo''_1580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1580 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_front'45'lo''_1580
      v2 v6 v9 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_front'45'lo''_1580 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v9)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_514
         (coe v4))
      (coe
         du_front'45'rsp_1572 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ret-step
d_ret'45'step_1600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ret'45'step_1600 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                   ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_ret'45'step_1600
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_ret'45'step_1600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ret'45'step_1600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14
  = coe
      du_go_1674 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_ret'45'site'45'owes_1126
         v0 v1 v2 erased v9 v10 v12
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
            (coe v14))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.saved-cons
d_saved'45'cons_1646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1288 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_saved'45'cons_1646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                     ~v24 v25 ~v26 v27 ~v28 ~v29 ~v30
  = du_saved'45'cons_1646 v25 v27
du_saved'45'cons_1646 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_saved'45'cons_1646 v0 v1
  = coe
      seq (coe v1)
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1674 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25
  = du_go_1674
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go_1674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1674 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v17 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
               -> coe
                    du_go'45'sv_1694 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
                    (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
                    (coe v14) (coe v16) (coe v18)
                    (coe
                       du_saved'45'cons_1646
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'stack_1356
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'seg'45'wf_1682
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                                (coe v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.go-sv
d_go'45'sv_1694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_1694 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27 v28
  = du_go'45'sv_1694
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26 v28
du_go'45'sv_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_1694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v17 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> coe
                           du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                           (coe v5) (coe v6) (coe v7) (coe v8)
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 (coe v10)))
                           (coe
                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_1966
                              (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                                 (coe v2))
                              v3 v7 v8 v9 v10 v13 v14 v16 v18 v20 v11 erased erased erased erased
                              erased
                              (coe
                                 MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1904
                                 v2 v3 v7 v8 v9 v10
                                 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                                    (coe v12))
                                 v11 erased)
                              erased)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.hpost
d_hpost_1708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1708 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.call-step
d_call'45'step_1736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'step_1736 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12
                    ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_call'45'step_1736
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_call'45'step_1736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'step_1736 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15
  = coe
      du_go_1774 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14) (coe v15)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_call'45'site'45'shape_1114
         v0 v1 v2 erased v11 v12
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
            (coe v15))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1774 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24
  = du_go_1774
      v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go_1774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1774 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v17 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  seq (coe v23)
                                  (coe
                                     du_ccc'45'step'45'bs_1462 (coe v0) (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1628
                                        (coe v6)
                                        (coe
                                           du_lo''_1798 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_front'45'lo''_1804 (coe v1) (coe v2) (coe v4) (coe v5)
                                           (coe v6) (coe v10) (coe v11) (coe v12) (coe v13)
                                           (coe v14)))
                                     (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2026
                                        (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                                           (coe v5))
                                        v6 v10 v11 v12 v16 v18 v20 v13 erased erased erased erased
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1156
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                                              (coe v13))
                                           (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92
                                              (coe v16))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78
                                              (coe v18))
                                           erased)
                                        erased
                                        (coe
                                           du_lo''_1798 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_lo'''8804'lo_1800 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_front'45'lo''_1804 (coe v1) (coe v2) (coe v4) (coe v5)
                                           (coe v6) (coe v10) (coe v11) (coe v12) (coe v13)
                                           (coe v14))
                                        (coe
                                           du_lo'''8804'rsp_1802 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_fits_1794 (coe v1) (coe v5) (coe v6) (coe v10)
                                           (coe v11) (coe v12) (coe v13) (coe v14))
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
                                           v5 v6 v10 v11 v12
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                                              (coe v2))
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                                              (coe v14))
                                           v13)
                                        erased)
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.room
d_room_1792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_room_1792 v11 v12 v17 v18 v19 v20 v21
du_room_1792 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1792 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1870
      v0 v1 v2 v3 v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v6))
      v5 erased (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.fits
d_fits_1794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1794 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_fits_1794 v2 v11 v12 v17 v18 v19 v20 v21
du_fits_1794 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1794 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v0))
      (coe
         du_room_1792 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-rsp
d_front'45'rsp_1796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29
  = du_front'45'rsp_1796 v11 v12 v17 v18 v19 v20 v21
du_front'45'rsp_1796 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1796 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v1))
      (coe
         du_room_1792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'
d_lo''_1798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1798 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_lo''_1798 v2 v6 v9 v12 v19
du_lo''_1798 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer
du_lo''_1798 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤lo
d_lo'''8804'lo_1800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1800 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29
  = du_lo'''8804'lo_1800 v2 v6 v9 v12 v19
du_lo'''8804'lo_1800 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1800 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤rsp
d_lo'''8804'rsp_1802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1802 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29
  = du_lo'''8804'rsp_1802 v2 v6 v9 v12 v19
du_lo'''8804'rsp_1802 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1802 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-lo'
d_front'45'lo''_1804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1804 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29
  = du_front'45'lo''_1804 v2 v6 v9 v11 v12 v17 v18 v19 v20 v21
du_front'45'lo''_1804 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_514
         (coe v4))
      (coe
         du_front'45'rsp_1796 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.step-eq
d_step'45'eq_1806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_1806 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1814 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.callfn-step
d_callfn'45'step_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_callfn'45'step_1844 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11
                      v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_callfn'45'step_1844
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_callfn'45'step_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_callfn'45'step_1844 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16
  = coe
      du_go_1880 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14) (coe v15) (coe v16)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_emitted'45'call'45'fn'45'resolves_1084
         (coe v0) (coe v1) (coe v2) (coe v11) (coe v12) (coe v14)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
            (coe v16)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1880 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25
  = du_go_1880
      v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1880 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16
  = case coe v16 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1628
                (coe v6)
                (coe du_lo''_1896 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_front'45'lo''_1902 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                   (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)))
             (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
                   (coe v13)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call'45'fn_2046
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v5))
                v6 v10 v11 v12 v13 v17 v14 erased erased erased
                (coe du_lo''_1896 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_lo'''8804'lo_1898 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_front'45'lo''_1902 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                   (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15))
                (coe
                   du_lo'''8804'rsp_1900 (coe v1) (coe v2) (coe v4) (coe v6)
                   (coe v12))
                (coe
                   du_fits_1892 (coe v1) (coe v5) (coe v6) (coe v10) (coe v11)
                   (coe v12) (coe v13) (coe v14) (coe v15))
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
                   v5 v6 v10 v11 v12
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                      (coe v2))
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v15))
                   v14)
                erased)
             (coe v15)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.room
d_room_1890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1890 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_room_1890 v11 v12 v17 v18 v19 v20 v21 v22
du_room_1890 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1890 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1870
      v0 v1 v2 v3 v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
            (coe v5)))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v7))
      v6 erased (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.fits
d_fits_1892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1892 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_fits_1892 v2 v11 v12 v17 v18 v19 v20 v21 v22
du_fits_1892 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1892 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v0))
      (coe
         du_room_1890 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-rsp
d_front'45'rsp_1894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25
                    ~v26
  = du_front'45'rsp_1894 v11 v12 v17 v18 v19 v20 v21 v22
du_front'45'rsp_1894 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1894 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v1))
      (coe
         du_room_1890 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'
d_lo''_1896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1896 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
  = du_lo''_1896 v2 v6 v9 v12 v19
du_lo''_1896 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer
du_lo''_1896 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤lo
d_lo'''8804'lo_1898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1898 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26
  = du_lo'''8804'lo_1898 v2 v6 v9 v12 v19
du_lo'''8804'lo_1898 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1898 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤rsp
d_lo'''8804'rsp_1900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1900 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26
  = du_lo'''8804'rsp_1900 v2 v6 v9 v12 v19
du_lo'''8804'rsp_1900 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1900 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-lo'
d_front'45'lo''_1902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1902 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_front'45'lo''_1902 v2 v6 v9 v11 v12 v17 v18 v19 v20 v21 v22
du_front'45'lo''_1902 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1902 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_514
         (coe v4))
      (coe
         du_front'45'rsp_1894 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1904 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.cjmp-step
d_cjmp'45'step_1934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cjmp'45'step_1934 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                    v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_cjmp'45'step_1934
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_cjmp'45'step_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cjmp'45'step_1934 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_go'45'fl_1970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
         (coe v7) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_1970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_1970 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'fl_1970
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'fl_1970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_1970 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 (coe v10)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1800
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v2))
                v3 v7 v8 v9 v10 v14 v11 erased erased erased)
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1630
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'jmp_1574
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
                   (coe v2))
                v3 v5 v6 v7 v8 v9 v10 v11 erased erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1980 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1992 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.branch-step
d_branch'45'step_2016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'step_2016 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                      v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_branch'45'step_2016
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_branch'45'step_2016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'step_2016 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_go'45'sv_2132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_2054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_2054 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26 v27
                ~v28
  = du_go'45'fl_2054
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v27
du_go'45'fl_2054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_2054 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      0 -> case coe v14 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1816
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v2))
                       v3 v7 v8 v9 v10 (0 :: Integer) v15 v11 erased erased erased erased)
                    (coe v12)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1630
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
                       (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'scratch'45'zero_1590
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
                          (coe v2))
                       v3 v5 v6 v7 v8 v9 v10 v11 erased erased erased erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v15 = subInt (coe v13) (coe (1 :: Integer)) in
           coe
             (case coe v14 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                  -> coe
                       du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1816
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                             (coe v2))
                          v3 v7 v8 v9 v10 v13 v16 v11 erased erased erased erased)
                       (coe v12)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1830
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                             (coe v2))
                          v3 v7 v8 v9 v10 v15 v11 erased erased erased)
                       (coe v12)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2066 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2088 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2104 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2118 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2132 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'sv_2132
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'sv_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2132 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v14
        -> coe
             du_go'45'fl_2054 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v14)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v7) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.tag-branch-step
d_tag'45'branch'45'step_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'branch'45'step_2170 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                             ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_tag'45'branch'45'step_2170
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_tag'45'branch'45'step_2170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'branch'45'step_2170 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14
  = coe
      du_go'45'loc_2332 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2202 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
            (coe v14)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2202 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
               (coe v14))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2202 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24
  = du_wits_2202 v0 v1 v2 v17 v18 v22
du_wits_2202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2202 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_branch'45'tag'45'scrutinee'45'wf_4384
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_2212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_2212 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27
                ~v28 ~v29 v30 ~v31
  = du_go'45'fl_2212
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26 v30
du_go'45'fl_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_2212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15
  = case coe v14 of
      0 -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1848
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v2))
                       v3 v7 v8 v9 v10 v13 (0 :: Integer) v16 v11 erased erased erased
                       erased erased erased)
                    (coe v12)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1630
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
                       (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'tag'45'zero_1608
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
                          (coe v2))
                       v3 v5 v6 v7 v8 v9 v10 v13 v11 erased erased erased erased erased
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v16 = subInt (coe v14) (coe (1 :: Integer)) in
           coe
             (case coe v15 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                  -> coe
                       du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1848
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                             (coe v2))
                          v3 v7 v8 v9 v10 v13 v14 v17 v11 erased erased erased erased erased
                          erased)
                       (coe v12)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1864
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                             (coe v2))
                          v3 v7 v8 v9 v10 v13 v16 v11 erased erased erased erased erased)
                       (coe v12)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2230 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2262 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2288 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2312 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2312 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2332 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27
                 ~v28
  = du_go'45'loc_2332
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26
du_go'45'loc_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2332 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      seq (coe v13)
      (coe
         du_go'45'fl_2212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v13) (coe v14)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
            (coe v7) (coe v10)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_2346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1082
d_dc_2346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28
  = du_dc_2346 v21
du_dc_2346 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1082
du_dc_2346 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.addr-val
d_addr'45'val_2348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_2348 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-heap
d_rd'45'heap_2350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'heap_2350 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_2366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1082
d_dc_2366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28 ~v29
  = du_dc_2366 v21
du_dc_2366 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1082
du_dc_2366 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.spc
d_spc_2368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spc_2368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29
  = du_spc_2368
du_spc_2368 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spc_2368
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3392
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.st-cf
d_st'45'cf_2370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'cf_2370 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rdi-val
d_rdi'45'val_2374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2374 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-stack
d_rd'45'stack_2382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'stack_2382 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.scratch-dec-step
d_scratch'45'dec'45'step_2400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'dec'45'step_2400 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
                              ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_scratch'45'dec'45'step_2400
      v1 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_scratch'45'dec'45'step_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_scratch'45'dec'45'step_2400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = coe
      du_go'45'sv_2434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2434 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'sv_2434
      v1 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'sv_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2434 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v14
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1876
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v3))
                v4 v8 v9 v10 v14 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1892
                   v3 v4 v8 v9 v10
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v12))
                   v11 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
                   v3 v4 v8 v9 v10
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_46
                      (coe v1))
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v12))
                   v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.count-inc-step
d_count'45'inc'45'step_2470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'inc'45'step_2470 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                            ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_count'45'inc'45'step_2470
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_count'45'inc'45'step_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_count'45'inc'45'step_2470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'sv_2504 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2504 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'sv_2504
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'sv_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2504 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v13
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1888
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v2))
                v3 v7 v8 v9 v13 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1914
                   v2 v3 v7 v8 v9
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v11))
                   v10 erased))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.out-nz-step
d_out'45'nz'45'step_2540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_out'45'nz'45'step_2540 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10
                         v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_out'45'nz'45'step_2540
      v0 v1 v2 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_out'45'nz'45'step_2540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_out'45'nz'45'step_2540 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14
  = coe
      du_ccc'45'step'45'bs_1462 (coe v1) (coe v4) (coe v6) (coe v7)
      (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_382))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'out'45'nz_1900
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
            (coe v5))
         v6 v10 v11 v12
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_wd_2570 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
               (coe v14)))
         v13 erased erased erased
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
            v5 v6 v10 v11 v12
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_42
               (coe v3))
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
               (coe v14))
            v13))
      (coe v14)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wd
d_wd_2570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wd_2570 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wd_2570 v0 v1 v2 v17 v18 v21
du_wd_2570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wd_2570 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_out'45'nz'45'output'45'word_4204
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-step
d_load'45'indirect'45'step_2588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'step_2588 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                                ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_load'45'indirect'45'step_2588
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_load'45'indirect'45'step_2588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'step_2588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13
  = coe
      du_go'45'loc_2734 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2618 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
            (coe v13)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2618 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
               (coe v13))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2618 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wits_2618 v0 v1 v2 v17 v18 v21
du_wits_2618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2618 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'target'45'wf_4476
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_2626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_2626 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26 v27
                 ~v28
  = du_go'45'mem_2626
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26 v27
du_go'45'mem_2626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_2626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1614
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v2))
                v3 v7 v8 v9 v12 v15 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1156
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                      (coe v10))
                   v12 v15 erased)
                erased)
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1630
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect_1542
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
                   (coe v2))
                v3 v5 v6 v7 v8 v9 v12 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1160
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                      (coe v10))
                   v12 v13)
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2642 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2664 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_2682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_2682 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                   v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 v27
                   v28 ~v29
  = du_go'45'stack_2682
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v25 v27 v28
du_go'45'stack_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_2682 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1630
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v2))
                       v3 v7 v8 v9 v12 v13 v18 v10 erased erased erased erased v17 erased)
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2702 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2702 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2734 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26
  = du_go'45'loc_2734
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26
du_go'45'loc_2734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2734 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v14 v15
        -> coe
             du_go'45'stack_2682 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3392)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v8)))
                v15)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v14
        -> coe
             du_go'45'mem_2626 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v14) (coe v13 v14 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_430
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)) v14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-suc-step
d_load'45'indirect'45'suc'45'step_2766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'step_2766 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                       v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22
                                       ~v23
  = du_load'45'indirect'45'suc'45'step_2766
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_load'45'indirect'45'suc'45'step_2766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'step_2766 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13
  = coe
      du_go'45'loc_2912 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2796 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
            (coe v13)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2796 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
               (coe v13))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2796 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wits_2796 v0 v1 v2 v17 v18 v21
du_wits_2796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2796 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'suc'45'target'45'wf_4514
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_2804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_2804 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26 v27
                 ~v28
  = du_go'45'mem_2804
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26 v27
du_go'45'mem_2804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_2804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1644
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v2))
                v3 v7 v8 v9 v12 v15 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1156
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                      (coe v10))
                   (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v12)) v15
                   erased)
                erased)
             (coe v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1630
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect'45'suc_1558
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1832
                   (coe v2))
                v3 v5 v6 v7 v8 v9 v12 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1160
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                      (coe v10))
                   (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v12)) v13)
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2820 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2842 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_2860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_2860 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                   v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 v27
                   v28 ~v29
  = du_go'45'stack_2860
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v25 v27 v28
du_go'45'stack_2860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_2860 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1660
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v2))
                       v3 v7 v8 v9 v12 v13 v18 v10 erased erased erased erased v17 erased)
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2880 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2912 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26
  = du_go'45'loc_2912
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26
du_go'45'loc_2912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2912 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v14 v15
        -> coe
             du_go'45'stack_2860 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3414)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v8)))
                (addInt (coe (1 :: Integer)) (coe v15)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v14
        -> coe
             du_go'45'mem_2804 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v14) (coe v13 v14 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_430
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v14)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-from-slot-step
d_load'45'from'45'slot'45'step_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'from'45'slot'45'step_2946 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                    ~v23 ~v24
  = du_load'45'from'45'slot'45'step_2946
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_load'45'from'45'slot'45'step_2946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'from'45'slot'45'step_2946 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12 v13
  = coe
      du_go'45'mem_2982 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_2982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_2982 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_2982
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_2982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_2982 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1674
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3436
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2992 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.restore-input-step
d_restore'45'input'45'step_3020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restore'45'input'45'step_3020 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_restore'45'input'45'step_3020
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_restore'45'input'45'step_3020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restore'45'input'45'step_3020 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13
  = coe
      du_go'45'mem_3056 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3056 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_3056
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_3056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3056 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1688
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3436
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3066 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.worklist-pop-step
d_worklist'45'pop'45'step_3094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_worklist'45'pop'45'step_3094 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                               ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_worklist'45'pop'45'step_3094
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_worklist'45'pop'45'step_3094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_worklist'45'pop'45'step_3094 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13
  = coe
      du_go'45'mem_3130 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3130 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_3130
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_3130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1702
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3436
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3140 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-step
d_store'45'indirect'45'step_3166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'step_3166 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_store'45'indirect'45'step_3166
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_store'45'indirect'45'step_3166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'step_3166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      du_go'45'ptr_3200 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_3200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_3200 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'ptr_3200
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'ptr_3200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_3200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1758
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v3))
                       v4 v8 v9 v10 v15 v16 v11 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3392))
                       erased)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1742
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v3))
                       v4 v8 v9 v10 v15 v11 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1160
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                             (coe v11))
                          v15
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'inbounds_4434
                             (coe v0) (coe v1) (coe v8) (coe v9) (coe v15)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                                (coe v12))))
                       erased)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3210 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3226 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-suc-step
d_store'45'indirect'45'suc'45'step_3260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'step_3260 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21
                                        ~v22 ~v23
  = du_store'45'indirect'45'suc'45'step_3260
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_store'45'indirect'45'suc'45'step_3260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'step_3260 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      du_go'45'ptr_3294 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_3294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_3294 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'ptr_3294
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'ptr_3294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_3294 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1786
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v3))
                       v4 v8 v9 v10 v15 v16 v11 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3414))
                       erased)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1770
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v3))
                       v4 v8 v9 v10 v15 v11 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1160
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_654
                             (coe v11))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v15))
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'suc'45'inbounds_4454
                             (coe v0) (coe v1) (coe v8) (coe v9)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                                (coe v12))))
                       erased)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3304 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3320 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-external
d_sigop'45'external_3360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'external_3360 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                         v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
                         v27
  = du_sigop'45'external_3360
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_sigop'45'external_3360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'external_3360 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_3396 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.contract
d_contract_3392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_3392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_contract_3392
      v11 v12 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_contract_3392 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_3392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_2000
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v11))
      erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1064
         (coe v11))
      v12 v10 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lbl
d_lbl_3394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lbl_3394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25
           ~v26 ~v27
  = du_lbl_3394 v22
du_lbl_3394 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_lbl_3394 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
      (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_3396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_3396 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
           v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_rec_3396
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_rec_3396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_3396 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      v4 v3 v5 v6 v7
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         v1
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
         (coe du_lbl_3394 (coe v12)) v9)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_3392 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
               (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13) (coe v14)
               (coe v15))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1082
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.log≡
d_log'8801'_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_3398 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.goal
d_goal_3402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_3402 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-step
d_sigop'45'step_3432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'step_3432 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                     v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
  = du_sigop'45'step_3432
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
du_sigop'45'step_3432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'step_3432 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14
  = coe
      du_route_3470 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.SigOp.Info.du_sigop'45'owner_402
         (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v12)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.route
d_route_3470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_route_3470 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
             ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_route_3470
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_route_3470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_route_3470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_rec_3486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                      (coe v13) (coe v14) (coe v16))))
             erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
        -> coe
             du_sigop'45'external_3360 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.eqe
d_eqe_3480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqe_3480 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.contract
d_contract_3482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_3482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
                v27
  = du_contract_3482 v11 v12 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_contract_3482 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_3482 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_1980
      v0 v1 v2 v3 v4 v5 v6 v7 v8
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
         (coe v10))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1064
         (coe v10))
      v11 v9 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.pl
d_pl_3484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 -> AgdaAny
d_pl_3484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13
          ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_pl_3484 v11 v12 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_pl_3484 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 -> AgdaAny
du_pl_3484 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_contract_3482 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rec
d_rec_3486 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_3486 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
           v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_rec_3486
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_rec_3486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_3486 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      v4 v3 v5 v6 v7
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         v1
         (coe
            du_pl_3484 (coe v2) (coe v3) (coe v6) (coe v7) (coe v8) (coe v9)
            (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15))
         v9)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_3482 (coe v2) (coe v3) (coe v6) (coe v7) (coe v8)
               (coe v9) (coe v10) (coe v11) (coe v12) (coe v13) (coe v14)
               (coe v15))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1082
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.goal
d_goal_3488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_3488 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.log≡
d_log'8801'_3490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny ->
    [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_3490 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-agree
d_events'45'agree_3516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_3516 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18 v19 v20
  = du_events'45'agree_3516
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'agree_3516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree_3516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18
  = case coe v11 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> let v19 = subInt (coe v11) (coe (1 :: Integer)) in
           coe
             (coe
                du_go'45'h_3598 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v19)
                (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                (coe v18)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_432
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running
d_events'45'running_3534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running_3534 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21
  = du_events'45'running_3534
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'running_3534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running_3534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18
  = coe
      du_go_3632 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246 (coe v14)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v15)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running-fetch
d_events'45'running'45'fetch_3554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'fetch_3554 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
                                  v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_events'45'running'45'fetch_3554
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_events'45'running'45'fetch_3554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'fetch_3554 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1468
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1478
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe
             du_load'45'indirect'45'step_2588 (coe v0) (coe v1) (coe v2)
             (coe v6) (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe
             du_load'45'indirect'45'suc'45'step_2766 (coe v0) (coe v1) (coe v2)
             (coe v6) (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v20
        -> coe
             du_load'45'from'45'slot'45'step_2946 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1716
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3436
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe
             du_store'45'indirect'45'step_3166 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe
             du_store'45'indirect'45'suc'45'step_3260 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1578
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                   (coe v19)))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v20
        -> coe
             du_restore'45'input'45'step_3020 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1542
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe
             du_call'45'step_1736 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
             (coe v7) (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1554
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1730
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3436
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v20
        -> coe
             du_worklist'45'pop'45'step_3094 (coe v0) (coe v1) (coe v6) (coe v9)
             (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1566
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v20 v21 v22
        -> coe
             du_sigop'45'step_3432 (coe v1) (coe v8) (coe v9) (coe v10)
             (coe
                (\ v23 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v21) (coe v22) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v20 v21 v22
        -> case coe v21 of
             MAlonzo.Code.Once.Type.C_fits'45'int_202
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_1978
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_1938
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                             (coe v19))
                          v18 erased))
                    (coe v19)
             MAlonzo.Code.Once.Type.C_fits'45'float_204
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                       (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_1990
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_1950
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                             (coe v19))
                          v18 erased))
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v20
        -> coe
             du_go_4300 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v13) (coe v14) (coe v15) (coe v16) (coe v20) (coe v18)
             (coe v19)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v1)
                (coe v14) (coe v20))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1588
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1600
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_1926
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19))
                   v18 erased))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v20 v21
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v20
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4120
                (coe v2) (coe v10)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                (coe v20)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1844
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19))
                   v18 erased))
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2070
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_760
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_760
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_760
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1058
                   (coe v19))
                (\ v21 v22 ->
                   coe
                     MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_764
                     (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
                        (coe v19))
                     v21)
                (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_770
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1056
                      (coe v19)))
                erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1844
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19))
                   v18 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_1960
                   v9 v10 v14 v15 v16
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
                      (coe v19))
                   v18))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1488
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1498
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
               -> coe
                    du_scratch'45'dec'45'step_2400 (coe v1) (coe v4) (coe v6) (coe v9)
                    (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1518
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1508
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
               -> coe
                    du_count'45'inc'45'step_2470 (coe v1) (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_382
               -> coe
                    du_out'45'nz'45'step_2540 (coe v0) (coe v1) (coe v2) (coe v4)
                    (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v21
               -> coe
                    du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1530
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                          (coe v9))
                       v10 v14 v15 v16 v21 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v21
               -> coe
                    du_cjmp'45'step_1934 (coe v1) (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v21
               -> coe
                    du_branch'45'step_2016 (coe v1) (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v21
               -> coe
                    du_tag'45'branch'45'step_2170 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe v9) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v21 v22
               -> coe
                    du_thunk'45'step_1530 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                    (coe v7) (coe v9) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v22) (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v21
               -> coe
                    du_ret'45'step_1600 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9)
                    (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v21
               -> coe
                    du_callfn'45'step_1844 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                    (coe v7) (coe v9) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v21
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-h
d_go'45'h_3598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'h_3598 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20 v21 ~v22
  = du_go'45'h_3598
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_go'45'h_3598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'h_3598 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19
  = if coe v19
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      else coe
             du_events'45'running_3534 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v17) (coe v18)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_3632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3632 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 ~v21 v22 ~v23
  = du_go_3632
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v22
du_go_3632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3632 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
        -> coe
             du_events'45'running'45'fetch_3554 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v20) (coe v17) (coe v18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_events'45'running'45'end_1236
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_4300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_4300 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go_4300
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go_4300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_4300 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1462 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v22 ->
                   coe
                     du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2004
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
                   (coe v9))
                v10 v14 v15 v16 v17
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
                      (coe v6))
                   (coe v14) (coe v21))
                v18 erased erased erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.has-body
d_has'45'body_4314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_has'45'body_4314 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_has'45'body_4314 v0 v1 v2 v17 v19 v21
du_has'45'body_4314 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_has'45'body_4314 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'code'45'addr'45'has'45'body_1156
      v0 v1 v2 erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_432
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
            (coe v5)))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_434
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1066
            (coe v5)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v3)) v4 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.no-body
d_no'45'body_4324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'body_4324 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.nj
d_nj_4336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nj_4336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28 ~v29
  = du_nj_4336
du_nj_4336 :: AgdaAny
du_nj_4336 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-agree-start
d_events'45'agree'45'start_4764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree'45'start_4764 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25 v26
                                ~v27 ~v28 ~v29 ~v30
  = du_events'45'agree'45'start_4764
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v25 v26
du_events'45'agree'45'start_4764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree'45'start_4764 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
               (coe v6))
            (coe du_i_4808 (coe v17)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_4828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19) (coe v20) (coe v21) (coe v22) (coe v23))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.i
d_i_4808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_i_4808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
         ~v26 ~v27 ~v28 ~v29 ~v30
  = du_i_4808 v19
du_i_4808 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_i_4808 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.room
d_room_4810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_4810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
            ~v27 v28 ~v29 ~v30
  = du_room_4810 v11 v12 v16 v17 v18 v19 v20 v26 v28
du_room_4810 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_4810 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1858
      v0 v1 v2 v3 v4 v5 v7 v6
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.fits
d_fits_4812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_4812 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
            ~v27 ~v28 ~v29 ~v30
  = du_fits_4812 v2 v11 v12 v16 v17 v18 v19 v20 v26
du_fits_4812 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_4812 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v6)))
      (coe
         du_room_4810 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-rsp
d_front'45'rsp_4814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_4814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    v26 ~v27 ~v28 ~v29 ~v30
  = du_front'45'rsp_4814 v11 v12 v16 v17 v18 v19 v20 v26
du_front'45'rsp_4814 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_4814 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v1))
      (coe
         du_room_4810 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'
d_lo''_4816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_4816 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 ~v27
            ~v28 ~v29 ~v30
  = du_lo''_4816 v2 v6 v9 v12 v18 v19
du_lo''_4816 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> Integer
du_lo''_4816 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤lo
d_lo'''8804'lo_4818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_4818 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29 ~v30
  = du_lo'''8804'lo_4818 v2 v6 v9 v12 v18 v19
du_lo'''8804'lo_4818 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_4818 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤rsp
d_lo'''8804'rsp_4820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_4820 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29 ~v30
  = du_lo'''8804'rsp_4820 v2 v6 v9 v12 v18 v19
du_lo'''8804'rsp_4820 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_4820 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-lo'
d_front'45'lo''_4822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_4822 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
                     ~v27 ~v28 ~v29 ~v30
  = du_front'45'lo''_4822 v2 v6 v9 v11 v12 v16 v17 v18 v19 v20 v26
du_front'45'lo''_4822 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_4822 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_494
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_512
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v8)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_514
         (coe v4))
      (coe
         du_front'45'rsp_4814 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.bs
d_bs_4824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs_4824 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11 v12 ~v13
          ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 ~v27
          ~v28 ~v29 ~v30
  = du_bs_4824 v2 v6 v9 v11 v12 v16 v17 v18 v19 v20 v26
du_bs_4824 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bs_4824 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'start_1944
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1830
         (coe v3))
      v4 v5 v6 v7 v8 v9 erased erased
      (coe
         du_lo''_4816 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7) (coe v8))
      (coe
         du_lo'''8804'lo_4818 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7)
         (coe v8))
      (coe
         du_front'45'lo''_4822 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))
      (coe
         du_lo'''8804'rsp_4820 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7)
         (coe v8))
      (coe
         du_fits_4812 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1882
         v3 v4 v5 v6 v7
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
            (coe v1))
         v10 v9)
      erased erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.inv₁
d_inv'8321'_4826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032
d_inv'8321'_4826 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 v17 ~v18 v19 ~v20 v21 v22 v23 ~v24 v25 v26
                 ~v27 ~v28 ~v29 ~v30
  = du_inv'8321'_4826 v1 v16 v17 v19 v21 v22 v23 v25 v26
du_inv'8321'_4826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1032
du_inv'8321'_4826 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.C_mkFlatInv_1070
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2844
         (coe v0) (coe du_i_4808 (coe v3)) (coe v1) (coe v2) (coe v4))
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_cl'45'step_2464
         (coe v0) (coe du_i_4808 (coe v3)) (coe v1) (coe v2) (coe v4)
         (coe v5))
      (MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.d_flat'45'regtag'45'step_1640
         (coe v0) (coe du_i_4808 (coe v3)) (coe v1) (coe v2) (coe v6))
      v7
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_442
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_432
            (coe v8))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_434
            (coe v8))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_438
            (coe v8))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_372
            (coe du_i_4808 (coe v3)) v2
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_440
               (coe v8))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_4828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_4828 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25 v26 ~v27 ~v28 ~v29 ~v30
  = du_rec_4828
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v25 v26
du_rec_4828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_4828 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19 v20 v21 v22 v23
  = coe
      du_events'45'agree_3516 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1628
         (coe v10)
         (coe
            du_lo''_4816 (coe v2) (coe v4) (coe v7) (coe v10) (coe v16)
            (coe v17))
         (coe
            du_front'45'lo''_4822 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10)
            (coe v14) (coe v15) (coe v16) (coe v17) (coe v18) (coe v23)))
      (coe v11) (coe v12) (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v1
         (coe du_i_4808 (coe v17)) v14 v15)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_bs_4824 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10) (coe v14)
            (coe v15) (coe v16) (coe v17) (coe v18) (coe v23)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_bs_4824 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10) (coe v14)
               (coe v15) (coe v16) (coe v17) (coe v18) (coe v23))))
      (coe
         du_inv'8321'_4826 (coe v1) (coe v14) (coe v15) (coe v17) (coe v19)
         (coe v20) (coe v21) (coe v22) (coe v23))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.result
d_result_4830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_4830 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.step-eq
d_step'45'eq_4832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1656 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_462 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_632 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_734 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_416 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_4832 = erased
