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
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockStep
d_BlockStep_34 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 -> ()
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer
d_blk'45'len_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'len_76 v8
du_blk'45'len_76 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer
du_blk'45'len_76 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView
d_HeapView_384 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slots
d_slots_654 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_slots_654 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_slots_654 v2
du_slots_654 :: Integer -> Integer -> Integer
du_slots_654 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.HDom
d_HDom_758 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 -> ()
d_HDom_758 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.caddr
d_caddr_760 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_760 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.dom-below
d_dom'45'below_762 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_762 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.front-lo
d_front'45'lo_764 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_764 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr
d_haddr_766 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 -> Integer
d_haddr_766 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-inj
d_haddr'45'inj_768 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_768 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-suc
d_haddr'45'suc_770 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_770 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.hfront
d_hfront_772 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_772 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.lo
d_lo_774 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_774 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.code-eq
d_code'45'eq_822 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_822 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.dataCorr
d_dataCorr_824 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dataCorr_824 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.pc-off
d_pc'45'off_826 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_826 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.ret-eq
d_ret'45'eq_828 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  AgdaAny
d_ret'45'eq_828 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-closure
d_inv'45'closure_832 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  AgdaAny
d_inv'45'closure_832 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1048
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-env
d_inv'45'env_834 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  AgdaAny
d_inv'45'env_834 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1054
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-ev
d_inv'45'ev_836 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_836 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-left
d_inv'45'left_838 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'left_838 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-regtag
d_inv'45'regtag_840 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524
d_inv'45'regtag_840 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1050
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-run
d_inv'45'run_842 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418
d_inv'45'run_842 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-started
d_inv'45'started_844 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_inv'45'started_844 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-wf
d_inv'45'wf_846 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
d_inv'45'wf_846 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.ArithEnv
d_ArithEnv_850 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_ArithEnv_850 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.EvExtractor
d_EvExtractor_852 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_EvExtractor_852 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events
d_run'45'events_854 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  [AgdaAny] -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events_854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'events_854 v8 v9 v10
du_run'45'events_854 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  [AgdaAny] -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events_854 v0 v1 v2
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_442
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_444
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-emit
d_run'45'emit_890 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_890 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-ir
d_run'45'ir_892 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_892 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_436
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-linked
d_run'45'linked_894 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_894 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-reach
d_run'45'reach_896 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_360
d_run'45'reach_896 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_442
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-tbl
d_run'45'tbl_898 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_898 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_434
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.arith-sigop-contract
d_arith'45'sigop'45'contract_914 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arith'45'sigop'45'contract_914 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_2058
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.bss
d_bss_916 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_842
d_bss_916 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.call-room
d_call'45'room_918 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_call'45'room_918 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1948
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.count-no-wrap
d_count'45'no'45'wrap_920 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_920 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1992
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.external-sigop-contract
d_external'45'sigop'45'contract_922 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_external'45'sigop'45'contract_922 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_2078
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.float-fits
d_float'45'fits_924 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_924 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_2028
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.heap-room
d_heap'45'room_926 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'room_926 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1922
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lit-fits
d_lit'45'fits_928 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_928 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_2016
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lo-fits
d_lo'45'fits_930 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_930 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_2038
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.reg-range
d_reg'45'range_932 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reg'45'range_932 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.ret-no-wrap
d_ret'45'no'45'wrap_934 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_934 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1982
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.scratch-dec-guarded
d_scratch'45'dec'45'guarded_936 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'dec'45'guarded_936 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1970
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.stack-room
d_stack'45'room_938 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'room_938 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1936
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.sts
d_sts_940 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1470
d_sts_940 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.tag-fits
d_tag'45'fits_942 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_942 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_2004
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.compile-trace
d_compile'45'trace_950 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [AgdaAny]
d_compile'45'trace_950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_compile'45'trace_950 v8
du_compile'45'trace_950 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [AgdaAny]
du_compile'45'trace_950 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'trace_108
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.memory
d_memory_1004 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_memory_1004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_memory_1004 v9
du_memory_1004 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Integer -> Maybe Integer
du_memory_1004 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_memory_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.rreg
d_rreg_1008 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_rreg_1008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_rreg_1008 v9
du_rreg_1008 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> AgdaAny -> Integer
du_rreg_1008 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.in1-reg
d_in1'45'reg_1040 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_in1'45'reg_1040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_in1'45'reg_1040 v6
du_in1'45'reg_1040 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_in1'45'reg_1040 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_44
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sp-reg
d_sp'45'reg_1046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_sp'45'reg_1046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_sp'45'reg_1046 v6
du_sp'45'reg_1046 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_sp'45'reg_1046 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.enter-call
d_enter'45'call_1056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_enter'45'call_1056 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enter'45'call_1056 v1
du_enter'45'call_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_enter'45'call_1056 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_960 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch
d_fetch_1062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_fetch_1062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_fetch_1062
du_fetch_1062 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
du_fetch_1062 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-fn
d_find'45'fn_1064 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
d_find'45'fn_1064 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'fn_1064 v1
du_find'45'fn_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
du_find'45'fn_1064 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-thunk
d_find'45'thunk_1066 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_1066 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'thunk_1066 v1
du_find'45'thunk_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_1066 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-exec-instr
d_flat'45'exec'45'instr_1068 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1068 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_flat'45'exec'45'instr_1068 v1
du_flat'45'exec'45'instr_1068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1068 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label
d_find'45'label_1070 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_1070 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'label_1070 v1
du_find'45'label_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_1070 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.readLoc
d_readLoc_1080 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readLoc_1080
du_readLoc_1080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1080
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatWF
d_FlatWF_1086 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_FlatWF_1086 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sv-below
d_sv'45'below_1092 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_sv'45'below_1092 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatRegTag
d_FlatRegTag_1106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_FlatRegTag_1106 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Frame
d_Frame_1122 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_Frame_1122 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RetMatch
d_RetMatch_1132 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.event-of
d_event'45'of_1320 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_event'45'of_1320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_event'45'of_1320
du_event'45'of_1320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_event'45'of_1320
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_504
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events
d_flat'45'events_1322 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events_1322 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_flat'45'events_1322 v1
du_flat'45'events_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events_1322 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_510 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-fetch
d_flat'45'events'45'fetch_1324 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events'45'fetch_1324 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_flat'45'events'45'fetch_1324 v1
du_flat'45'events'45'fetch_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events'45'fetch_1324 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-step
d_flat'45'events'45'step_1326 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flat'45'events'45'step_1326 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_flat'45'events'45'step_1326 v1
du_flat'45'events'45'step_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flat'45'events'45'step_1326 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.call≢thunk
d_call'8802'thunk_1332 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_call'8802'thunk_1332 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.callfn≢thunk
d_callfn'8802'thunk_1340 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_callfn'8802'thunk_1340 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.ret≢thunk
d_ret'8802'thunk_1348 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_ret'8802'thunk_1348 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.left-post
d_left'45'post_1476 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'post_1476 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.EventsIH
d_EventsIH_1488 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  Integer -> ()
d_EventsIH_1488 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ccc-step-bs
d_ccc'45'step'45'bs_1524 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccc'45'step'45'bs_1524 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                         ~v11 v12 ~v13 v14 v15 v16 v17 v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25
                         ~v26 ~v27 ~v28
  = du_ccc'45'step'45'bs_1524
      v1 v8 v12 v14 v15 v16 v17 v18 v20 v21 v22
du_ccc'45'step'45'bs_1524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccc'45'step'45'bs_1524 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
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
               du_rec_1562 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe v10))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_1562 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_1562 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 v14 v15 v16 v17 v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26 ~v27
           ~v28
  = du_rec_1562 v1 v12 v14 v15 v16 v17 v18 v20 v21 v22
du_rec_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_1562 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      v2 v1 v3 v4 v5
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v0
         v7 v5 v6)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1074
         (coe v0) (coe v7) (coe v5) (coe v6) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.result
d_result_1564 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_1564 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.log≡
d_log'8801'_1566 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_1566 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.thunk-step
d_thunk'45'step_1594 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'step_1594 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12
                     ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_thunk'45'step_1594
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_thunk'45'step_1594 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'step_1594 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17
  = coe
      du_ccc'45'step'45'bs_1524 (coe v1) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
         (coe v7)
         (coe
            du_lo''_1638 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_front'45'lo''_1644 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17)))
      (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 (coe v14)
            (coe v15)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1922
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
            (coe v6))
         v7 v11 v12 v13 v14 v15
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_lnk_1628 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
               (coe v14) (coe v15) (coe v17)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_pend_1630 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
               (coe v14) (coe v15) (coe v17)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_pend_1630 (coe v0) (coe v1) (coe v2) (coe v11) (coe v12)
                  (coe v14) (coe v15) (coe v17))))
         v16 erased erased
         (coe
            du_lo''_1638 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_lo'''8804'lo_1640 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_front'45'lo''_1644 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
            (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
            (coe v17))
         (coe
            du_lo'''8804'rsp_1642 (coe v2) (coe v3) (coe v5) (coe v7) (coe v13)
            (coe v15))
         (coe
            du_fits_1634 (coe v2) (coe v6) (coe v7) (coe v11) (coe v12)
            (coe v13) (coe v14) (coe v15) (coe v16) (coe v17))
         erased
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
            v6 v7 v11 v12 v13
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
               (coe v3))
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
               (coe v17))
            v16)
         erased erased)
      (coe v17)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lnk
d_lnk_1628 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lnk_1628 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 ~v16 v17 v18 ~v19 v20 v21 ~v22 v23 ~v24 ~v25
  = du_lnk_1628 v0 v1 v2 v17 v18 v20 v21 v23
du_lnk_1628 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lnk_1628 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'link_2384
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.pend
d_pend_1630 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pend_1630 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 v20 v21 ~v22 v23 ~v24 ~v25
  = du_pend_1630 v0 v1 v2 v17 v18 v20 v21 v23
du_pend_1630 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pend_1630 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'ret_2410
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.room
d_room_1632 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25
  = du_room_1632 v11 v12 v17 v18 v19 v20 v21 v22 v23 v25
du_room_1632 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1632 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1936
      v0 v1 v2 v3 v4 v6
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v8))
      v7
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v9)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.fits
d_fits_1634 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1634 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_fits_1634 v2 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_fits_1634 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1634 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v7)))
      (coe
         du_room_1632 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-rsp
d_front'45'rsp_1636 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_front'45'rsp_1636 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_front'45'rsp_1636 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1636 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v1))
      (coe
         du_room_1632 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'
d_lo''_1638 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1638 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo''_1638 v2 v6 v9 v12 v19 v21
du_lo''_1638 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> Integer
du_lo''_1638 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'lo_1640 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1640 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo'''8804'lo_1640 v2 v6 v9 v12 v19 v21
du_lo'''8804'lo_1640 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1640 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'rsp_1642 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1642 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_lo'''8804'rsp_1642 v2 v6 v9 v12 v19 v21
du_lo'''8804'rsp_1642 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1642 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_front'45'lo''_1644 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1644 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_front'45'lo''_1644
      v2 v6 v9 v11 v12 v17 v18 v19 v20 v21 v22 v23
du_front'45'lo''_1644 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1644 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
         (coe v4))
      (coe
         du_front'45'rsp_1636 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ret-step
d_ret'45'step_1664 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ret'45'step_1664 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                   ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_ret'45'step_1664
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_ret'45'step_1664 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ret'45'step_1664 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14
  = coe
      du_go_1738 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_ret'45'site'45'owes_1114
         v0 v1 v2 erased v9 v10 v12
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
            (coe v14))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.saved-cons
d_saved'45'cons_1710 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1276 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_saved'45'cons_1710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                     ~v24 v25 ~v26 v27 ~v28 ~v29 ~v30
  = du_saved'45'cons_1710 v25 v27
du_saved'45'cons_1710 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_saved'45'cons_1710 v0 v1
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
d_go_1738 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1738 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25
  = du_go_1738
      v0 v1 v2 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go_1738 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1738 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v17 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
               -> coe
                    du_go'45'sv_1758 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
                    (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
                    (coe v14) (coe v16) (coe v18)
                    (coe
                       du_saved'45'cons_1710
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v10)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'stack_1344
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'seg'45'wf_1672
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                                (coe v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.go-sv
d_go'45'sv_1758 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_1758 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27 v28
  = du_go'45'sv_1758
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26 v28
du_go'45'sv_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_1758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v17 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> coe
                           du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v4)
                           (coe v5) (coe v6) (coe v7) (coe v8)
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 (coe v10)))
                           (coe
                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_1962
                              (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                                 (coe v2))
                              v3 v7 v8 v9 v10 v13 v14 v16 v18 v20 v11 erased erased erased erased
                              erased
                              (coe
                                 MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1982
                                 v2 v3 v7 v8 v9 v10
                                 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                                    (coe v12))
                                 v11 erased)
                              erased)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.hpost
d_hpost_1772 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
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
d_hpost_1772 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.call-step
d_call'45'step_1800 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'step_1800 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12
                    ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_call'45'step_1800
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_call'45'step_1800 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'step_1800 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15
  = coe
      du_go_1838 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14) (coe v15)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_call'45'site'45'shape_1102
         v0 v1 v2 erased v11 v12
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
            (coe v15))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1838 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1838 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24
  = du_go_1838
      v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go_1838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
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
                                     du_ccc'45'step'45'bs_1524 (coe v0) (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
                                        (coe v6)
                                        (coe
                                           du_lo''_1862 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_front'45'lo''_1868 (coe v1) (coe v2) (coe v4) (coe v5)
                                           (coe v6) (coe v10) (coe v11) (coe v12) (coe v13)
                                           (coe v14)))
                                     (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2022
                                        (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                                           (coe v5))
                                        v6 v10 v11 v12 v16 v18 v20 v13 erased erased erased erased
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                                              (coe v13))
                                           (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84
                                              (coe v16))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78
                                              (coe v18))
                                           erased)
                                        erased
                                        (coe
                                           du_lo''_1862 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_lo'''8804'lo_1864 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_front'45'lo''_1868 (coe v1) (coe v2) (coe v4) (coe v5)
                                           (coe v6) (coe v10) (coe v11) (coe v12) (coe v13)
                                           (coe v14))
                                        (coe
                                           du_lo'''8804'rsp_1866 (coe v1) (coe v2) (coe v4) (coe v6)
                                           (coe v12))
                                        (coe
                                           du_fits_1858 (coe v1) (coe v5) (coe v6) (coe v10)
                                           (coe v11) (coe v12) (coe v13) (coe v14))
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
                                           v5 v6 v10 v11 v12
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                                              (coe v2))
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                                              (coe v14))
                                           v13)
                                        erased)
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.room
d_room_1856 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1856 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_room_1856 v11 v12 v17 v18 v19 v20 v21
du_room_1856 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1856 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1948
      v0 v1 v2 v3 v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284)
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v6))
      v5 erased (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.fits
d_fits_1858 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1858 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_fits_1858 v2 v11 v12 v17 v18 v19 v20 v21
du_fits_1858 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1858 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v0))
      (coe
         du_room_1856 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-rsp
d_front'45'rsp_1860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29
  = du_front'45'rsp_1860 v11 v12 v17 v18 v19 v20 v21
du_front'45'rsp_1860 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1860 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v1))
      (coe
         du_room_1856 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'
d_lo''_1862 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1862 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28 ~v29
  = du_lo''_1862 v2 v6 v9 v12 v19
du_lo''_1862 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer
du_lo''_1862 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'lo_1864 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1864 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29
  = du_lo'''8804'lo_1864 v2 v6 v9 v12 v19
du_lo'''8804'lo_1864 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1864 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'rsp_1866 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1866 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29
  = du_lo'''8804'rsp_1866 v2 v6 v9 v12 v19
du_lo'''8804'rsp_1866 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1866 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_front'45'lo''_1868 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1868 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29
  = du_front'45'lo''_1868 v2 v6 v9 v11 v12 v17 v18 v19 v20 v21
du_front'45'lo''_1868 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1868 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
         (coe v4))
      (coe
         du_front'45'rsp_1860 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.step-eq
d_step'45'eq_1870 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_1870 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1878 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1878 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.callfn-step
d_callfn'45'step_1908 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_callfn'45'step_1908 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11
                      v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_callfn'45'step_1908
      v0 v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_callfn'45'step_1908 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_callfn'45'step_1908 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16
  = coe
      du_go_1944 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14) (coe v15) (coe v16)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_emitted'45'call'45'fn'45'resolves_1072
         (coe v0) (coe v1) (coe v2) (coe v11) (coe v12) (coe v14)
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
            (coe v16)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1944 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 ~v13 v14
          v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25
  = du_go_1944
      v1 v2 v6 v8 v9 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1944 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16
  = case coe v16 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
                (coe v6)
                (coe du_lo''_1960 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_front'45'lo''_1966 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                   (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)))
             (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
                   (coe v13)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call'45'fn_2042
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v5))
                v6 v10 v11 v12 v13 v17 v14 erased erased erased
                (coe du_lo''_1960 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_lo'''8804'lo_1962 (coe v1) (coe v2) (coe v4) (coe v6) (coe v12))
                (coe
                   du_front'45'lo''_1966 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                   (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15))
                (coe
                   du_lo'''8804'rsp_1964 (coe v1) (coe v2) (coe v4) (coe v6)
                   (coe v12))
                (coe
                   du_fits_1956 (coe v1) (coe v5) (coe v6) (coe v10) (coe v11)
                   (coe v12) (coe v13) (coe v14) (coe v15))
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
                   v5 v6 v10 v11 v12
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                      (coe v2))
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v15))
                   v14)
                erased)
             (coe v15)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.room
d_room_1954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_room_1954 v11 v12 v17 v18 v19 v20 v21 v22
du_room_1954 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_1954 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1948
      v0 v1 v2 v3 v4
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
            (coe v5)))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v7))
      v6 erased (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.fits
d_fits_1956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_1956 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_fits_1956 v2 v11 v12 v17 v18 v19 v20 v21 v22
du_fits_1956 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_1956 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v0))
      (coe
         du_room_1954 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-rsp
d_front'45'rsp_1958 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_1958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25
                    ~v26
  = du_front'45'rsp_1958 v11 v12 v17 v18 v19 v20 v21 v22
du_front'45'rsp_1958 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_1958 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v1))
      (coe
         du_room_1954 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'
d_lo''_1960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_1960 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
  = du_lo''_1960 v2 v6 v9 v12 v19
du_lo''_1960 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer
du_lo''_1960 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'lo_1962 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_1962 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26
  = du_lo'''8804'lo_1962 v2 v6 v9 v12 v19
du_lo'''8804'lo_1962 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_1962 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'rsp_1964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_1964 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26
  = du_lo'''8804'rsp_1964 v2 v6 v9 v12 v19
du_lo'''8804'rsp_1964 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_1964 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_front'45'lo''_1966 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_1966 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 ~v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_front'45'lo''_1966 v2 v6 v9 v11 v12 v17 v18 v19 v20 v21 v22
du_front'45'lo''_1966 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_1966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
         (coe v4))
      (coe
         du_front'45'rsp_1958 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_1968 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_1968 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.cjmp-step
d_cjmp'45'step_1998 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cjmp'45'step_1998 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                    v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_cjmp'45'step_1998
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_cjmp'45'step_1998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cjmp'45'step_1998 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_go'45'fl_2034 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
         (coe v8) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_2034 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_2034 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'fl_2034
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'fl_2034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_2034 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 (coe v11)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1796
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v2))
                v3 v8 v9 v10 v11 v15 v12 erased erased erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1656
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
             (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'jmp_1600
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
                   (coe v2))
                v3 v6 v7 v8 v9 v10 v11 v12 erased erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2044 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2044 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2056 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.branch-step
d_branch'45'step_2080 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'step_2080 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                      v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_branch'45'step_2080
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_branch'45'step_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'step_2080 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13
  = coe
      du_go'45'sv_2196 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_2118 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_2118 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26 v27 ~v28
  = du_go'45'fl_2118
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v27
du_go'45'fl_2118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_2118 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15
  = case coe v14 of
      0 -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1812
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v2))
                       v3 v8 v9 v10 v11 (0 :: Integer) v16 v12 erased erased erased
                       erased)
                    (coe v13)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1656
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
                       (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'scratch'45'zero_1616
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
                          (coe v2))
                       v3 v6 v7 v8 v9 v10 v11 v12 erased erased erased erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v16 = subInt (coe v14) (coe (1 :: Integer)) in
           coe
             (case coe v15 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                  -> coe
                       du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1812
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                             (coe v2))
                          v3 v8 v9 v10 v11 v14 v17 v12 erased erased erased erased)
                       (coe v13)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1826
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                             (coe v2))
                          v3 v8 v9 v10 v11 v16 v12 erased erased erased)
                       (coe v13)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2130 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2152 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2152 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2168 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2168 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2182 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2196 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2196 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'sv_2196
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'sv_2196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2196 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v15
        -> coe
             du_go'45'fl_2118 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v8) (coe v11))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v15 v16 v17
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.tag-branch-step
d_tag'45'branch'45'step_2234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'branch'45'step_2234 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                             ~v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_tag'45'branch'45'step_2234
      v0 v1 v2 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_tag'45'branch'45'step_2234 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'branch'45'step_2234 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15
  = coe
      du_go'45'loc_2396 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14) (coe v15)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2266 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
            (coe v15)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2266 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
               (coe v15))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2266 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2266 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24
  = du_wits_2266 v0 v1 v2 v17 v18 v22
du_wits_2266 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2266 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_branch'45'tag'45'scrutinee'45'wf_4382
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_2276 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
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
d_go'45'fl_2276 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27 ~v28
                ~v29 v30 ~v31
  = du_go'45'fl_2276
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26 v30
du_go'45'fl_2276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_2276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16
  = case coe v15 of
      0 -> case coe v16 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1844
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v2))
                       v3 v8 v9 v10 v11 v14 (0 :: Integer) v17 v12 erased erased erased
                       erased erased erased)
                    (coe v13)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1656
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
                       (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
                    (coe v4)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'tag'45'zero_1634
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
                          (coe v2))
                       v3 v6 v7 v8 v9 v10 v11 v14 v12 erased erased erased erased erased
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v17 = subInt (coe v15) (coe (1 :: Integer)) in
           coe
             (case coe v16 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                  -> coe
                       du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1844
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                             (coe v2))
                          v3 v8 v9 v10 v11 v14 v15 v18 v12 erased erased erased erased erased
                          erased)
                       (coe v13)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1860
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                             (coe v2))
                          v3 v8 v9 v10 v11 v14 v17 v12 erased erased erased erased erased)
                       (coe v13)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2294 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2294 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2326 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
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
d_hpost_2326 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2352 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2352 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2376 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2376 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2396 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2396 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 v26 ~v27 ~v28
  = du_go'45'loc_2396
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25 v26
du_go'45'loc_2396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2396 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = coe
      seq (coe v14)
      (coe
         du_go'45'fl_2276 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v13) (coe v14) (coe v15)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
            (coe v8) (coe v11)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_2410 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dc_2410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28
  = du_dc_2410 v21
du_dc_2410 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_dc_2410 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.addr-val
d_addr'45'val_2412 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_2412 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-heap
d_rd'45'heap_2414 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'heap_2414 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_2430 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dc_2430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28 ~v29
  = du_dc_2430 v21
du_dc_2430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_dc_2430 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.spc
d_spc_2432 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spc_2432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28 ~v29
  = du_spc_2432
du_spc_2432 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spc_2432
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3390
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.st-cf
d_st'45'cf_2434 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'cf_2434 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rdi-val
d_rdi'45'val_2438 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_2438 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-stack
d_rd'45'stack_2446 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'stack_2446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.scratch-dec-step
d_scratch'45'dec'45'step_2464 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'dec'45'step_2464 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
                              ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_scratch'45'dec'45'step_2464
      v1 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_scratch'45'dec'45'step_2464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_scratch'45'dec'45'step_2464 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = coe
      du_go'45'sv_2498 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2498 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2498 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'sv_2498
      v1 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'sv_2498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2498 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v14
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_370))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1872
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v3))
                v4 v8 v9 v10 v14 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1970
                   v3 v4 v8 v9 v10
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v12))
                   v11 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
                   v3 v4 v8 v9 v10
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_46
                      (coe v1))
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v12))
                   v11))
             (coe v12)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.count-inc-step
d_count'45'inc'45'step_2534 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'inc'45'step_2534 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                            ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_count'45'inc'45'step_2534
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_count'45'inc'45'step_2534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_count'45'inc'45'step_2534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_go'45'sv_2568 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_2568 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_2568 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'sv_2568
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'sv_2568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_2568 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v13
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_376))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1884
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v2))
                v3 v7 v8 v9 v13 v10 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1992
                   v2 v3 v7 v8 v9
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v11))
                   v10 erased))
             (coe v11)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v13 v14 v15
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.out-nz-step
d_out'45'nz'45'step_2604 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_out'45'nz'45'step_2604 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10
                         v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_out'45'nz'45'step_2604
      v0 v1 v2 v6 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_out'45'nz'45'step_2604 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_out'45'nz'45'step_2604 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14
  = coe
      du_ccc'45'step'45'bs_1524 (coe v1) (coe v4) (coe v6) (coe v7)
      (coe v8) (coe v9) (coe v10) (coe v11)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_378))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'out'45'nz_1896
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
            (coe v5))
         v6 v10 v11 v12
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_wd_2634 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
               (coe v14)))
         v13 erased erased erased
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
            v5 v6 v10 v11 v12
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_42
               (coe v3))
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
               (coe v14))
            v13))
      (coe v14)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wd
d_wd_2634 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wd_2634 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wd_2634 v0 v1 v2 v17 v18 v21
du_wd_2634 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wd_2634 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_out'45'nz'45'output'45'word_4202
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-step
d_load'45'indirect'45'step_2652 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'step_2652 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                                ~v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_load'45'indirect'45'step_2652
      v0 v1 v2 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
du_load'45'indirect'45'step_2652 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'step_2652 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13 v14
  = coe
      du_go'45'loc_2798 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2682 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
            (coe v14)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2682 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
               (coe v14))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2682 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2682 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wits_2682 v0 v1 v2 v17 v18 v21
du_wits_2682 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2682 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'target'45'wf_4474
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_2690 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_2690 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26 v27 ~v28
  = du_go'45'mem_2690
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26 v27
du_go'45'mem_2690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_2690 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1610
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v2))
                v3 v8 v9 v10 v13 v16 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                      (coe v11))
                   v13 v16 erased)
                erased)
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1656
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
             (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect_1568
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
                   (coe v2))
                v3 v6 v7 v8 v9 v10 v13 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                      (coe v11))
                   v13 v14)
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2706 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2706 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2728 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2728 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_2746 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_2746 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                   v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 v27
                   v28 ~v29
  = du_go'45'stack_2746
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v25 v27 v28
du_go'45'stack_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_2746 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1626
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v2))
                       v3 v7 v8 v9 v12 v13 v18 v10 erased erased erased erased v17 erased)
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2766 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
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
d_hpost_2766 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2798 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2798 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26
  = du_go'45'loc_2798
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26
du_go'45'loc_2798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2798 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
        -> coe
             du_go'45'stack_2746 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v15) (coe v16)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3390)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_426
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
                v16)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
        -> coe
             du_go'45'mem_2690 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v15) (coe v14 v15 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_428
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)) v15)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-suc-step
d_load'45'indirect'45'suc'45'step_2830 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'step_2830 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                       v8 ~v9 ~v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22
                                       ~v23
  = du_load'45'indirect'45'suc'45'step_2830
      v0 v1 v2 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
du_load'45'indirect'45'suc'45'step_2830 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'step_2830 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14
  = coe
      du_go'45'loc_2976 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
      (coe v14)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_2860 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
            (coe v14)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_2860 (coe v0) (coe v1) (coe v2) (coe v10) (coe v11)
               (coe v14))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_2860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_2860 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wits_2860 v0 v1 v2 v17 v18 v21
du_wits_2860 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_2860 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'suc'45'target'45'wf_4512
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_2868 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_2868 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26 v27 ~v28
  = du_go'45'mem_2868
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26 v27
du_go'45'mem_2868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_2868 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v15 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1640
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v2))
                v3 v8 v9 v10 v13 v16 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                      (coe v11))
                   (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v13)) v16
                   erased)
                erased)
             (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_stuck'45'result_1656
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
             (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect'45'suc_1584
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1910
                   (coe v2))
                v3 v6 v7 v8 v9 v10 v13 v11 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                      (coe v11))
                   (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v13)) v14)
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2884 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2884 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2906 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_2906 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_2924 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_2924 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11
                   v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 v27
                   v28 ~v29
  = du_go'45'stack_2924
      v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24 v25 v27 v28
du_go'45'stack_2924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_2924 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v0) (coe v1) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1656
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v2))
                       v3 v7 v8 v9 v12 v13 v18 v10 erased erased erased erased v17 erased)
                    (coe v11)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_2944 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
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
d_hpost_2944 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_2976 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_2976 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26
  = du_go'45'loc_2976
      v1 v8 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v24 v26
du_go'45'loc_2976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_2976 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
        -> coe
             du_go'45'stack_2924 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v15) (coe v16)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3412)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_426
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
                (addInt (coe (1 :: Integer)) (coe v16)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
        -> coe
             du_go'45'mem_2868 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v15) (coe v14 v15 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_428
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v15)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-from-slot-step
d_load'45'from'45'slot'45'step_3010 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'from'45'slot'45'step_3010 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                    ~v23 ~v24
  = du_load'45'from'45'slot'45'step_3010
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_load'45'from'45'slot'45'step_3010 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'from'45'slot'45'step_3010 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12 v13
  = coe
      du_go'45'mem_3046 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_426
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3046 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_3046
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_3046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3046 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1670
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3434
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3056 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3056 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.restore-input-step
d_restore'45'input'45'step_3084 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restore'45'input'45'step_3084 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_restore'45'input'45'step_3084
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_restore'45'input'45'step_3084 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restore'45'input'45'step_3084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13
  = coe
      du_go'45'mem_3120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_426
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3120 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_3120
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_3120 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3120 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2272
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1684
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3434
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3130 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3130 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.worklist-pop-step
d_worklist'45'pop'45'step_3158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_worklist'45'pop'45'step_3158 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                               ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_worklist'45'pop'45'step_3158
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_worklist'45'pop'45'step_3158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_worklist'45'pop'45'step_3158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13
  = coe
      du_go'45'mem_3194 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_426
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v9)))
         v11)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3194 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24 v25 ~v26
  = du_go'45'mem_3194
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v25
du_go'45'mem_3194 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3194 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2290
                (coe v11))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1698
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v3))
                v4 v8 v9 v10 v11 v15 v12 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3434
                   (coe v0) (coe v9) (coe v11)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v13)))
                erased)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3204 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3204 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-step
d_store'45'indirect'45'step_3230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'step_3230 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_store'45'indirect'45'step_3230
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_store'45'indirect'45'step_3230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'step_3230 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12
  = coe
      du_go'45'ptr_3264 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_3264 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_3264 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'ptr_3264
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'ptr_3264 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_3264 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1754
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v3))
                       v4 v8 v9 v10 v15 v16 v11 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3390))
                       erased)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1738
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v3))
                       v4 v8 v9 v10 v15 v11 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                             (coe v11))
                          v15
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'inbounds_4432
                             (coe v0) (coe v1) (coe v8) (coe v9) (coe v15)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
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
d_hpost_3274 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3274 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3290 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3290 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-suc-step
d_store'45'indirect'45'suc'45'step_3324 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'step_3324 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21
                                        ~v22 ~v23
  = du_store'45'indirect'45'suc'45'step_3324
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
du_store'45'indirect'45'suc'45'step_3324 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'step_3324 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12
  = coe
      du_go'45'ptr_3358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v9)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_3358 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_3358 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
                 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'ptr_3358
      v0 v1 v8 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v24
du_go'45'ptr_3358 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_3358 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v14
        -> case coe v14 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v15 v16
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1782
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v3))
                       v4 v8 v9 v10 v15 v16 v11 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3412))
                       erased)
                    (coe v12)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v15
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v2) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v9)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1766
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v3))
                       v4 v8 v9 v10 v15 v11 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_650
                             (coe v11))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v15))
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'suc'45'inbounds_4452
                             (coe v0) (coe v1) (coe v8) (coe v9)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
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
d_hpost_3368 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3368 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3384 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3384 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-external
d_sigop'45'external_3424 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'external_3424 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                         v11 v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
                         v27
  = du_sigop'45'external_3424
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_sigop'45'external_3424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'external_3424 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_3460 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.contract
d_contract_3456 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_3456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_contract_3456
      v11 v12 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_contract_3456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_3456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_2078
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v11))
      erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1054
         (coe v11))
      v12 v10 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lbl
d_lbl_3458 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lbl_3458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25
           ~v26 ~v27
  = du_lbl_3458 v22
du_lbl_3458 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_lbl_3458 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
      (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_3460 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_3460 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
           v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_rec_3460
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_rec_3460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_3460 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      v4 v3 v5 v6 v7
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_442
         v1
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_432
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v8)))
         (coe du_lbl_3458 (coe v12)) v9)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_3456 (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
               (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13) (coe v14)
               (coe v15))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1074
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.log≡
d_log'8801'_3462 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_3462 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.goal
d_goal_3466 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_3466 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-step
d_sigop'45'step_3496 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'step_3496 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                     v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
  = du_sigop'45'step_3496
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
du_sigop'45'step_3496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'step_3496 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14
  = coe
      du_route_3534 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.SigOp.Info.du_sigop'45'owner_260
         (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v12)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.route
d_route_3534 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_route_3534 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
             ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_route_3534
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_route_3534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_route_3534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = case coe v15 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_rec_3550 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                      (coe v13) (coe v14) (coe v16))))
             erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
        -> coe
             du_sigop'45'external_3424 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.eqe
d_eqe_3544 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqe_3544 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.contract
d_contract_3546 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_3546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26
                v27
  = du_contract_3546 v11 v12 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_contract_3546 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_3546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_2058
      v0 v1 v2 v3 v4 v5 v6 v7 v8
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
         (coe v10))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'env_1054
         (coe v10))
      v11 v9 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.pl
d_pl_3548 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 -> AgdaAny
d_pl_3548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13
          ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_pl_3548 v11 v12 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_pl_3548 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 -> AgdaAny
du_pl_3548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_contract_3546 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rec
d_rec_3550 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_3550 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
           v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ~v25 ~v26 v27
  = du_rec_3550
      v1 v10 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v27
du_rec_3550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_3550 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      v4 v3 v5 v6 v7
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298
            (coe v10) (coe v11) (coe v12))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_444
         v1
         (coe
            du_pl_3548 (coe v2) (coe v3) (coe v6) (coe v7) (coe v8) (coe v9)
            (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15))
         v9)
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_3546 (coe v2) (coe v3) (coe v6) (coe v7) (coe v8)
               (coe v9) (coe v10) (coe v11) (coe v12) (coe v13) (coe v14)
               (coe v15))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1074
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298
            (coe v10) (coe v11) (coe v12))
         (coe v7) (coe v8) (coe v14))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.goal
d_goal_3552 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_3552 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.log≡
d_log'8801'_3554 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   AgdaAny ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log'8801'_3554 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.leave-step
d_leave'45'step_3580 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leave'45'step_3580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_leave'45'step_3580 v13
du_leave'45'step_3580 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_leave'45'step_3580 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-agree
d_events'45'agree_3632 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_3632 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18 v19 v20
  = du_events'45'agree_3632
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'agree_3632 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree_3632 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18
  = case coe v11 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> let v19 = subInt (coe v11) (coe (1 :: Integer)) in
           coe
             (coe
                du_go'45'h_3714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v19)
                (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                (coe v18)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_430
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running
d_events'45'running_3650 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running_3650 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21
  = du_events'45'running_3650
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'running_3650 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running_3650 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18
  = coe
      du_go_3750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246 (coe v14)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v15)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running-fetch
d_events'45'running'45'fetch_3670 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'fetch_3670 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
                                  v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_events'45'running'45'fetch_3670
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_events'45'running'45'fetch_3670 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'fetch_3670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2254
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1464
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2256
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1474
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2258
        -> coe
             du_load'45'indirect'45'step_2652 (coe v0) (coe v1) (coe v2)
             (coe v6) (coe v9) (coe v10) (coe v11)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2260
        -> coe
             du_load'45'indirect'45'suc'45'step_2830 (coe v0) (coe v1) (coe v2)
             (coe v6) (coe v9) (coe v10) (coe v11)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2262 v20
        -> coe
             du_load'45'from'45'slot'45'step_3010 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2264 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1712
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3434
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2266
        -> coe
             du_store'45'indirect'45'step_3230 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2268
        -> coe
             du_store'45'indirect'45'suc'45'step_3324 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2270 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1574
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                   (coe v19)))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2272 v20
        -> coe
             du_restore'45'input'45'step_3084 (coe v0) (coe v1) (coe v6)
             (coe v9) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2274 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2276 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2278 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1538
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2280 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2282
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2284
        -> coe
             du_call'45'step_1800 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
             (coe v7) (coe v9) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2286 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1550
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2288 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1726
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3434
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2290 v20
        -> coe
             du_worklist'45'pop'45'step_3158 (coe v0) (coe v1) (coe v6) (coe v9)
             (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2292 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1562
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2298 v20 v21 v22
        -> coe
             du_sigop'45'step_3496 (coe v1) (coe v8) (coe v9) (coe v10)
             (coe
                (\ v23 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v21) (coe v22) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2304 v20 v21 v22
        -> case coe v21 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2304
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_1974
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_2016
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                             (coe v19))
                          v18 erased))
                    (coe v19)
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2304
                       (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_1986
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_2028
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                             (coe v19))
                          v18 erased))
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2306 v20
        -> coe
             du_go_4418 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v13) (coe v14) (coe v15) (coe v16) (coe v20) (coe v18)
             (coe v19)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v1)
                (coe v14) (coe v20))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2308
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v20 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v20)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1584
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2310 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1596
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_2004
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19))
                   v18 erased))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2312 v20 v21
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2314 v20
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4096
                (coe v2) (coe v10)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                (coe v20)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1922
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19))
                   v18 erased))
             (coe
                (\ v21 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2066
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_762
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_762
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_762
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1048
                   (coe v19))
                (\ v21 v22 ->
                   coe
                     MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_766
                     (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
                        (coe v19))
                     v21)
                (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_772
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1046
                      (coe v19)))
                erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1922
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19))
                   v18 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_2038
                   v9 v10 v14 v15 v16
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
                      (coe v19))
                   v18))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2316 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2318 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_366
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1484
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_368
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1494
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_370
               -> coe
                    du_scratch'45'dec'45'step_2464 (coe v1) (coe v4) (coe v6) (coe v9)
                    (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_372
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1514
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_374
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1504
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_376
               -> coe
                    du_count'45'inc'45'step_2534 (coe v1) (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_378
               -> coe
                    du_out'45'nz'45'step_2604 (coe v0) (coe v1) (coe v2) (coe v4)
                    (coe v6) (coe v9) (coe v10)
                    (coe
                       (\ v21 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v21)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v21
               -> coe
                    du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1526
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
                          (coe v9))
                       v10 v14 v15 v16 v21 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v21
               -> coe
                    du_cjmp'45'step_1998 (coe v1) (coe v6) (coe v9) (coe v10) (coe v11)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v21
               -> coe
                    du_branch'45'step_2080 (coe v1) (coe v6) (coe v9) (coe v10)
                    (coe v11)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v21
               -> coe
                    du_tag'45'branch'45'step_2234 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe v9) (coe v10) (coe v11)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v21 v22
               -> coe
                    du_thunk'45'step_1594 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                    (coe v7) (coe v9) (coe v10)
                    (coe
                       (\ v23 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v23)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v22) (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v21
               -> coe
                    du_ret'45'step_1664 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9)
                    (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v21
               -> coe
                    du_callfn'45'step_1908 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                    (coe v7) (coe v9) (coe v10)
                    (coe
                       (\ v22 ->
                          coe
                            du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                            (coe v11)))
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v21
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2244
               -> coe du_leave'45'step_3580 (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2322 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-h
d_go'45'h_3714 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'h_3714 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20 v21 ~v22
  = du_go'45'h_3714
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_go'45'h_3714 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'h_3714 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19
  = if coe v19
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      else coe
             du_events'45'running_3650 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v17) (coe v18)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_3750 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3750 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 ~v21 v22 ~v23
  = du_go_3750
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v22
du_go_3750 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3750 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
        -> coe
             du_events'45'running'45'fetch_3670 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v20) (coe v17) (coe v18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_events'45'running'45'end_1230
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_4418 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_4418 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go_4418
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go_4418 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_4418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1524 (coe v1) (coe v6) (coe v10)
             (coe
                (\ v22 ->
                   coe
                     du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v22)
                     (coe v11)))
             (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2306
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2000
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
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
d_has'45'body_4432 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_has'45'body_4432 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_has'45'body_4432 v0 v1 v2 v17 v19 v21
du_has'45'body_4432 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_has'45'body_4432 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'code'45'addr'45'has'45'body_1144
      v0 v1 v2 erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_434
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
            (coe v5)))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_436
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1056
            (coe v5)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v3)) v4 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.no-body
d_no'45'body_4442 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'body_4442 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.nj
d_nj_4454 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nj_4454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28 ~v29
  = du_nj_4454
du_nj_4454 :: AgdaAny
du_nj_4454 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-agree-start
d_events'45'agree'45'start_4904 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree'45'start_4904 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25 v26
                                ~v27 ~v28 ~v29 ~v30 ~v31
  = du_events'45'agree'45'start_4904
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v25 v26
du_events'45'agree'45'start_4904 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree'45'start_4904 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
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
            (coe du_i_4950 (coe v17)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_4970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19) (coe v20) (coe v21) (coe v22) (coe v23))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.i
d_i_4950 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_i_4950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
         ~v26 ~v27 ~v28 ~v29 ~v30 ~v31
  = du_i_4950 v19
du_i_4950 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
du_i_4950 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2320
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.room
d_room_4952 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_4952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
            ~v27 v28 ~v29 ~v30 ~v31
  = du_room_4952 v11 v12 v16 v17 v18 v19 v20 v26 v28
du_room_4952 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_4952 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1936
      v0 v1 v2 v3 v4 v5 v7 v6
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.fits
d_fits_4954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_4954 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
            ~v27 ~v28 ~v29 ~v30 ~v31
  = du_fits_4954 v2 v11 v12 v16 v17 v18 v19 v20 v26
du_fits_4954 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_4954 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
            (coe v0) (coe v6)))
      (coe
         du_room_4952 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-rsp
d_front'45'rsp_4956 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_4956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    v26 ~v27 ~v28 ~v29 ~v30 ~v31
  = du_front'45'rsp_4956 v11 v12 v16 v17 v18 v19 v20 v26
du_front'45'rsp_4956 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_4956 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v1))
      (coe
         du_room_4952 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'
d_lo''_4958 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_4958 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 ~v27
            ~v28 ~v29 ~v30 ~v31
  = du_lo''_4958 v2 v6 v9 v12 v18 v19
du_lo''_4958 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> Integer
du_lo''_4958 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'lo_4960 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_4960 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28 ~v29 ~v30 ~v31
  = du_lo'''8804'lo_4960 v2 v6 v9 v12 v18 v19
du_lo'''8804'lo_4960 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_4960 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_lo'''8804'rsp_4962 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_4962 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28 ~v29 ~v30 ~v31
  = du_lo'''8804'rsp_4962 v2 v6 v9 v12 v18 v19
du_lo'''8804'rsp_4962 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_4962 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
d_front'45'lo''_4964 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_4964 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
                     ~v27 ~v28 ~v29 ~v30 ~v31
  = du_front'45'lo''_4964 v2 v6 v9 v11 v12 v16 v17 v18 v19 v20 v26
du_front'45'lo''_4964 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_4964 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
         (coe v4))
      (coe
         du_front'45'rsp_4956 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.bs
d_bs_4966 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs_4966 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11 v12 ~v13
          ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 ~v27
          ~v28 ~v29 ~v30 ~v31
  = du_bs_4966 v2 v6 v9 v11 v12 v16 v17 v18 v19 v20 v26
du_bs_4966 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bs_4966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'start_1940
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1908
         (coe v3))
      v4 v5 v6 v7 v8 v9 erased erased
      (coe
         du_lo''_4958 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7) (coe v8))
      (coe
         du_lo'''8804'lo_4960 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7)
         (coe v8))
      (coe
         du_front'45'lo''_4964 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))
      (coe
         du_lo'''8804'rsp_4962 (coe v0) (coe v1) (coe v2) (coe v4) (coe v7)
         (coe v8))
      (coe
         du_fits_4954 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1960
         v3 v4 v5 v6 v7
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
            (coe v1))
         v10 v9)
      erased erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.inv₁
d_inv'8321'_4968 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020
d_inv'8321'_4968 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 v17 ~v18 v19 ~v20 v21 v22 v23 ~v24 v25 v26
                 ~v27 ~v28 ~v29 ~v30 ~v31
  = du_inv'8321'_4968 v1 v16 v17 v19 v21 v22 v23 v25 v26
du_inv'8321'_4968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1020
du_inv'8321'_4968 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.C_mkFlatInv_1062
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2862
         (coe v0) (coe du_i_4950 (coe v3)) (coe v1) (coe v2) (coe v4))
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_cl'45'step_2474
         (coe v0) (coe du_i_4950 (coe v3)) (coe v1) (coe v2) (coe v4)
         (coe v5))
      (MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.d_flat'45'regtag'45'step_1642
         (coe v0) (coe du_i_4950 (coe v3)) (coe v1) (coe v2) (coe v6))
      v7
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_444
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_434
            (coe v8))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_436
            (coe v8))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_440
            (coe v8))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_374
            (coe du_i_4950 (coe v3)) v2
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_442
               (coe v8))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_4970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_4970 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20 v21 v22 v23 ~v24 v25 v26 ~v27 ~v28 ~v29 ~v30
           ~v31
  = du_rec_4970
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v25 v26
du_rec_4970 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_4970 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19 v20 v21 v22 v23
  = coe
      du_events'45'agree_3632 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
         (coe v10)
         (coe
            du_lo''_4958 (coe v2) (coe v4) (coe v7) (coe v10) (coe v16)
            (coe v17))
         (coe
            du_front'45'lo''_4964 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10)
            (coe v14) (coe v15) (coe v16) (coe v17) (coe v18) (coe v23)))
      (coe v11) (coe v12) (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v1
         (coe du_i_4950 (coe v17)) v14 v15)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_bs_4966 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10) (coe v14)
            (coe v15) (coe v16) (coe v17) (coe v18) (coe v23)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_bs_4966 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10) (coe v14)
               (coe v15) (coe v16) (coe v17) (coe v18) (coe v23))))
      (coe
         du_inv'8321'_4968 (coe v1) (coe v14) (coe v15) (coe v17) (coe v19)
         (coe v20) (coe v21) (coe v22) (coe v23))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.result
d_result_4972 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_4972 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.step-eq
d_step'45'eq_4974 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1734 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_628 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_524 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_4974 = erased
