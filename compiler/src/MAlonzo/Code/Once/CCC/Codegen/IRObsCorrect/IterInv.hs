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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.IterInv where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Σ
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Bool
d_Bool_15 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.BeforeFrontier
d_BeforeFrontier_380 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState
d_FlatState_404 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatSteps
d_FlatSteps_408 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.InputAt
d_InputAt_424 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.ResultPlace
d_ResultPlace_438 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.chain-ctrls
d_chain'45'ctrls_474 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer
d_chain'45'ctrls_474 ~v0 ~v1 ~v2 = du_chain'45'ctrls_474
du_chain'45'ctrls_474 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer
du_chain'45'ctrls_474 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'ctrls_814 v4
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.chain-events
d_chain'45'events_480 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_chain'45'events_480 ~v0 ~v1 v2 = du_chain'45'events_480 v2
du_chain'45'events_480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_chain'45'events_480 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.emitted
d_emitted_544 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_emitted_544 v0 ~v1 = du_emitted_544 v0
du_emitted_544 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_emitted_544 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_1876
      (coe v0) v2 v3 v4 v5 v6
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.eventsAt
d_eventsAt_566 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_eventsAt_566 ~v0 ~v1 = du_eventsAt_566
du_eventsAt_566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_eventsAt_566 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_878
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.resultAt
d_resultAt_850 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_resultAt_850 ~v0 ~v1 = du_resultAt_850
du_resultAt_850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
du_resultAt_850 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_886
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.stopsAt
d_stopsAt_902 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> Bool
d_stopsAt_902 ~v0 ~v1 = du_stopsAt_902
du_stopsAt_902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> Bool
du_stopsAt_902 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_894
      v0 v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.⟪_⟫_
d_'10218'_'10219'__954 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  Integer -> MAlonzo.Code.Once.Internal.Trace.T_T_110
d_'10218'_'10219'__954 ~v0 ~v1 = du_'10218'_'10219'__954
du_'10218'_'10219'__954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  Integer -> MAlonzo.Code.Once.Internal.Trace.T_T_110
du_'10218'_'10219'__954 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_'10218'_'10219'__942
      v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.falloc
d_falloc_1048 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1048 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.fclosure
d_fclosure_1050 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1050 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.flink
d_flink_1052 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1052 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.floc
d_floc_1054 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_1054 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.fpc
d_fpc_1056 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1056 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Core.FlatState.fret
d_fret_1058 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1058 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._._+_
d__'43'__1686 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> Integer -> Integer
d__'43'__1686 ~v0 ~v1 = du__'43'__1686
du__'43'__1686 :: Integer -> Integer -> Integer
du__'43'__1686 = coe addInt
-- Once.CCC.Codegen.IRObsCorrect.IterInv._._×_
d__'215'__1694 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'__1694 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv._._≡_
d__'8801'__1702 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._._≤_
d__'8804'__1706 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.AllocMode
d_AllocMode_1730 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.IR
d_IR_1744 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.List
d_List_1752 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Maybe
d_Maybe_1754 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.length
d_length_1808 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
d_length_1808 ~v0 ~v1 = du_length_1808
du_length_1808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
du_length_1808 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.fst
d_fst_1828 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_1828 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.snd
d_snd_1830 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_1830 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.Nat
d_Nat_1856 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv._.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_1878 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_1878 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.BeforeFrontier
d_BeforeFrontier_2088 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState
d_FlatState_2112 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatSteps
d_FlatSteps_2116 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.InputAt
d_InputAt_2132 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.ResultPlace
d_ResultPlace_2146 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.chain-ctrls
d_chain'45'ctrls_2182 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer
d_chain'45'ctrls_2182 ~v0 ~v1 ~v2 = du_chain'45'ctrls_2182
du_chain'45'ctrls_2182 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  Integer
du_chain'45'ctrls_2182 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'ctrls_814 v4
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.chain-events
d_chain'45'events_2188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_chain'45'events_2188 ~v0 ~v1 v2 = du_chain'45'events_2188 v2
du_chain'45'events_2188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_chain'45'events_2188 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.du_chain'45'events_650
      (coe v0) v1 v3 v5
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.emitted
d_emitted_2252 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_emitted_2252 v0 ~v1 ~v2 = du_emitted_2252 v0
du_emitted_2252 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
du_emitted_2252 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_emitted_1876
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.eventsAt
d_eventsAt_2274 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_eventsAt_2274 ~v0 ~v1 v2 = du_eventsAt_2274 v2
du_eventsAt_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_eventsAt_2274 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eventsAt_878
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.resultAt
d_resultAt_2558 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_resultAt_2558 ~v0 ~v1 v2 = du_resultAt_2558 v2
du_resultAt_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
du_resultAt_2558 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_resultAt_886
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.stopsAt
d_stopsAt_2610 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> Bool
d_stopsAt_2610 ~v0 ~v1 v2 = du_stopsAt_2610 v2
du_stopsAt_2610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> Bool
du_stopsAt_2610 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_stopsAt_894
      (coe v0) v2 v3
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.⟪_⟫_
d_'10218'_'10219'__2662 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  Integer -> MAlonzo.Code.Once.Internal.Trace.T_T_110
d_'10218'_'10219'__2662 ~v0 ~v1 ~v2 = du_'10218'_'10219'__2662
du_'10218'_'10219'__2662 ::
  () ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  Integer -> MAlonzo.Code.Once.Internal.Trace.T_T_110
du_'10218'_'10219'__2662 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_'10218'_'10219'__942
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.falloc
d_falloc_2756 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_2756 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.fclosure
d_fclosure_2758 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_2758 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.flink
d_flink_2760 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_2760 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.floc
d_floc_2762 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_2762 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.fpc
d_fpc_2764 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_2764 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC._.FlatState.fret
d_fret_2766 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_2766 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.round
d_round_3410 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_round_3410 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11
  = du_round_3410 v1 v2 v3 v4 v5 v6 v10 v11
du_round_3410 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_round_3410 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_eval'7472'_866
      v0 v1 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v3))
      (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v4) (coe v3)) v5
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.loopFrom
d_loopFrom_3416 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_loopFrom_3416 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11
  = du_loopFrom_3416 v1 v2 v3 v4 v5 v6 v10 v11
du_loopFrom_3416 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_loopFrom_3416 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Internal.Iterative.du_iterRun_212
      (coe
         du_round_3410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
      (coe
         du_round_3410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor
d_Anchor_3422 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Anchor_3422
  = C_constructor_3492 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
                       MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (Integer ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.s₀
d_s'8320'_3458 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_s'8320'_3458 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.alloc₀
d_alloc'8320'_3460 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_alloc'8320'_3460 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.n≤₀
d_n'8804''8320'_3462 ::
  T_Anchor_3422 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804''8320'_3462 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.e
d_e_3464 :: T_Anchor_3422 -> AgdaAny
d_e_3464 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.fsF
d_fsF_3466 ::
  T_Anchor_3422 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fsF_3466 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.mf
d_mf_3468 :: T_Anchor_3422 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mf_3468 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.caf
d_caf_3470 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_caf_3470 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.placeF
d_placeF_3472 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_placeF_3472 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.cf-F
d_cf'45'F_3474 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'F_3474 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.ns-F
d_ns'45'F_3476 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ns'45'F_3476 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.hr-F
d_hr'45'F_3478 ::
  T_Anchor_3422 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hr'45'F_3478 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.mem0-F
d_mem0'45'F_3482 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem0'45'F_3482 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.bf0-F
d_bf0'45'F_3488 ::
  T_Anchor_3422 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf0'45'F_3488 v0
  = case coe v0 of
      C_constructor_3492 v1 v2 v3 v4 v5 v6 v7 v8 v11 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop.Anchor.left-F
d_left'45'F_3490 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'F_3490 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.alloc₀
d_alloc'8320'_3502 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_alloc'8320'_3502 v0 = coe d_alloc'8320'_3460 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.bf0-F
d_bf0'45'F_3504 ::
  T_Anchor_3422 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf0'45'F_3504 v0 = coe d_bf0'45'F_3488 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.caf
d_caf_3506 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_caf_3506 v0 = coe d_caf_3470 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.cf-F
d_cf'45'F_3508 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf'45'F_3508 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.e
d_e_3510 :: T_Anchor_3422 -> AgdaAny
d_e_3510 v0 = coe d_e_3464 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.fsF
d_fsF_3512 ::
  T_Anchor_3422 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fsF_3512 v0 = coe d_fsF_3466 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.hr-F
d_hr'45'F_3514 ::
  T_Anchor_3422 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hr'45'F_3514 v0 = coe d_hr'45'F_3478 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.left-F
d_left'45'F_3516 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'F_3516 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.mem0-F
d_mem0'45'F_3518 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem0'45'F_3518 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.mf
d_mf_3520 :: T_Anchor_3422 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mf_3520 v0 = coe d_mf_3468 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.ns-F
d_ns'45'F_3522 ::
  T_Anchor_3422 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ns'45'F_3522 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.n≤₀
d_n'8804''8320'_3524 ::
  T_Anchor_3422 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804''8320'_3524 v0 = coe d_n'8804''8320'_3462 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.placeF
d_placeF_3526 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_placeF_3526 v0 = coe d_placeF_3472 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._._.s₀
d_s'8320'_3528 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_s'8320'_3528 v0 = coe d_s'8320'_3458 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.FR
d_FR_3530 :: T_Anchor_3422 -> AgdaAny
d_FR_3530 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
      (coe d_alloc'8320'_3460 (coe v0))
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.fv
d_fv_3532 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fv_3532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_fv_3532 v10
du_fv_3532 ::
  T_Anchor_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_fv_3532 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_144
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_424
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
            (coe d_fsF_3466 (coe v0))))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv
d_RoundInv_3538 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_RoundInv_3538
  = C_constructor_3616 MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2262
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (Integer ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.pc
d_pc_3580 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc_3580 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.ret
d_ret_3582 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ret_3582 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.lnk
d_lnk_3584 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lnk_3584 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.nh
d_nh_3586 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh_3586 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.mode
d_mode_3588 ::
  T_RoundInv_3538 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mode_3588 v0
  = case coe v0 of
      C_constructor_3616 v5 v6 v9 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.inp
d_inp_3590 ::
  T_RoundInv_3538 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_2262
d_inp_3590 v0
  = case coe v0 of
      C_constructor_3616 v5 v6 v9 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.cf
d_cf_3592 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cf_3592 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.ns
d_ns_3594 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ns_3594 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.hr
d_hr_3596 ::
  T_RoundInv_3538 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hr_3596 v0
  = case coe v0 of
      C_constructor_3616 v5 v6 v9 v13 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.memF
d_memF_3600 ::
  T_RoundInv_3538 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_memF_3600 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.env
d_env_3602 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env_3602 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.mem0
d_mem0_3606 ::
  T_RoundInv_3538 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem0_3606 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.bf0
d_bf0_3612 ::
  T_RoundInv_3538 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf0_3612 v0
  = case coe v0 of
      C_constructor_3616 v5 v6 v9 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundInv.left
d_left_3614 ::
  T_RoundInv_3538 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left_3614 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun
d_RoundsRun_3626 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_RoundsRun_3626
  = C_constructor_3732 Integer
                       MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
                       MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
                       (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612)
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584)
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.steps
d_steps_3684 :: T_RoundsRun_3626 -> Integer
d_steps_3684 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.settle
d_settle_3686 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_3686 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.out-mode
d_out'45'mode_3688 ::
  T_RoundsRun_3626 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_3688 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.cont-alloc
d_cont'45'alloc_3690 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_3690 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.run
d_run_3692 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_336
d_run_3692 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.live
d_live_3694 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_3694 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.at-end
d_at'45'end_3700 ::
  T_RoundsRun_3626 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_3700 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.stops
d_stops_3702 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stops_3702 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.no-ret
d_no'45'ret_3704 ::
  T_RoundsRun_3626 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_3704 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.no-link
d_no'45'link_3706 ::
  T_RoundsRun_3626 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_3706 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.place
d_place_3712 ::
  T_RoundsRun_3626 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_612
d_place_3712 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.events
d_events_3714 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events_3714 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.log
d_log_3716 ::
  T_RoundsRun_3626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_3716 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.progress
d_progress_3718 ::
  T_RoundsRun_3626 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_progress_3718 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.mem0
d_mem0_3722 ::
  T_RoundsRun_3626 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem0_3722 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.frame
d_frame_3724 ::
  T_RoundsRun_3626 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame_3724 = erased
-- Once.CCC.Codegen.IRObsCorrect.IterInv.IterInvC.Loop._.RoundsRun.bf0
d_bf0_3730 ::
  T_RoundsRun_3626 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_584
d_bf0_3730 v0
  = case coe v0 of
      C_constructor_3732 v1 v2 v3 v4 v5 v8 v11 v14 v17 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
