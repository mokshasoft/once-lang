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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Simple where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Codegen.IRObsCorrect.Simple._.Σ
d_Σ_1 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.List
d_List_3 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.AbstractReg
d_AbstractReg_5 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.BeforeFrontier
d_BeforeFrontier_726 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.CellAt
d_CellAt_740 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.FlatSteps
d_FlatSteps_750 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.IRObsCorrectF
d_IRObsCorrectF_760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_760 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.InputAt
d_InputAt_764 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF
d_MachineRefinesObsF_768 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ResultPlace
d_ResultPlace_776 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValidAtWF
d_ValidAtWF_786 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized
d_ValueRealized_788 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.prim-sv
d_prim'45'sv_1078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_1078 ~v0 ~v1 ~v2 = du_prim'45'sv_1078
du_prim'45'sv_1078 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_1078 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_556
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.readLoc
d_readLoc_1092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1092 ~v0 ~v1 ~v2 = du_readLoc_1092
du_readLoc_1092 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1092
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1318 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1318 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1320 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
d_value'45'realized_1320 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3544
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.at-end
d_at'45'end_1378 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1378 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1380 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_1380 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.live
d_live_1382 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1382 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.no-link
d_no'45'link_1384 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1384 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.no-ret
d_no'45'ret_1386 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1386 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.out-mode
d_out'45'mode_1388 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1388 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3472
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.place
d_place_1390 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_1390 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3486
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.run
d_run_1392 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_1392 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3476
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.settle
d_settle_1394 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1394 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3470
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.steps
d_steps_1396 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  Integer
d_steps_1396 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3468
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._._≡_
d__'8801'__1766 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.AbstractInstr
d_AbstractInstr_1788 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal
d_Decimal_1808 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FitsInReg
d_FitsInReg_1816 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FitsInRegI
d_FitsInRegI_1818 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics
d_FrameSemantics_1820 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.HeapRef
d_HeapRef_1834 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.IR
d_IR_1840 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.IRTy
d_IRTy_1842 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.NatTr
d_NatTr_1860 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.StoredValue
d_StoredValue_1890 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.ValueLocation
d_ValueLocation_1898 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.WellFormedFI
d_WellFormedFI_1900 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.projTrace
d_projTrace_2014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_projTrace_2014 ~v0 = du_projTrace_2014
du_projTrace_2014 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_projTrace_2014 v0 v1 v2
  = coe MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_64 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple._.fst
d_fst_2016 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2016 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.snd
d_snd_2018 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2018 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.readReg
d_readReg_2020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readReg_2020 ~v0 = du_readReg_2020
du_readReg_2020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readReg_2020 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148 v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple._.sucLoc
d_sucLoc_2046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_2046 ~v0 = du_sucLoc_2046
du_sucLoc_2046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_2046 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 v1
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Nat
d_Nat_2076 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Int
d_Int_2078 a0 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_2098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_2098 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.⟦_⟧TI
d_'10214'_'10215'TI_2102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_'10214'_'10215'TI_2102 ~v0 = du_'10214'_'10215'TI_2102
du_'10214'_'10215'TI_2102 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
du_'10214'_'10215'TI_2102
  = coe MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal.exp10
d_exp10_2316 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_exp10_2316 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_exp10_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal.sig
d_sig_2318 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_sig_2318 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_sig_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics._≟F_
d__'8799'F__2756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__2756 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__88 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics._≺_
d__'8826'__2758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__2758 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.Frame
d_Frame_2760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_2760 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.float-format
d_float'45'format_2762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_2762 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_124 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-base
d_frame'45'base_2764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_2764 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_2766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_2766 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-word
d_frame'45'word_2768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_2768 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_2770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_2770 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_110
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.shift-base
d_shift'45'base_2772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_2772 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.shift-frame
d_shift'45'frame_2774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_2774 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-addr
d_slot'45'addr_2776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_2776 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_2778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_2778 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-injective
d_slot'45'injective_2780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_2780 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_2782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_2782 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-compare
d_'8826''45'compare_2784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_2784 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_144
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_2786 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-trans
d_'8826''45'trans_2788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_2788 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_134 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.HeapRef.ref-id
d_ref'45'id_2868 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 -> Integer
d_ref'45'id_2868 v0
  = coe MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.BeforeFrontier
d_BeforeFrontier_3656 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.CellAt
d_CellAt_3670 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.FlatSteps
d_FlatSteps_3680 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.IRObsCorrectF
d_IRObsCorrectF_3690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3690 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.InputAt
d_InputAt_3694 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF
d_MachineRefinesObsF_3698 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ResultPlace
d_ResultPlace_3706 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValidAtWF
d_ValidAtWF_3716 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized
d_ValueRealized_3718 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.evalᴰ
d_eval'7472'_3802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472'_3802 v0 ~v1 v2 v3 = du_eval'7472'_3802 v0 v2 v3
du_eval'7472'_3802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_eval'7472'_3802 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158 (coe v0))
      (coe v1) (coe v2)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.prim-sv
d_prim'45'sv_4008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_4008 ~v0 ~v1 ~v2 = du_prim'45'sv_4008
du_prim'45'sv_4008 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_4008 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_556
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.readLoc
d_readLoc_4022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_4022 ~v0 ~v1 ~v2 = du_readLoc_4022
du_readLoc_4022 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_4022
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4248 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4248 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF.value-realized
d_value'45'realized_4250 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422
d_value'45'realized_4250 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3544
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.at-end
d_at'45'end_4308 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4308 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.cont-alloc
d_cont'45'alloc_4310 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_cont'45'alloc_4310 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3474
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.live
d_live_4312 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4312 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.no-link
d_no'45'link_4314 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4314 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.no-ret
d_no'45'ret_4316 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4316 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.out-mode
d_out'45'mode_4318 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4318 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3472
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.place
d_place_4320 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_4320 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3486
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.run
d_run_4322 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_330
d_run_4322 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3476
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.settle
d_settle_4324 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4324 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3470
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.steps
d_steps_4326 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3422 ->
  Integer
d_steps_4326 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3468
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-id
d_obs'45'correct'45'id_4678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'id_4678 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
                            v11 v12 v13 v14 v15 v16 ~v17 v18 v19 ~v20
  = du_obs'45'correct'45'id_4678
      v0 v1 v2 v3 v8 v11 v12 v13 v14 v15 v16 v18 v19
du_obs'45'correct'45'id_4678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'id_4678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
         (1 :: Integer)
         (coe
            du_fs'8321'_4716 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
         v6
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               du_fs'8321'_4716 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
               (coe
                  v5 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
         (coe
            du_place_4792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)
            (coe v8) (coe v9) (coe v10) (coe v12)))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.regs'
d_regs''_4714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs''_4714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_regs''_4714 v14
du_regs''_4714 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_regs''_4714 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_4716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_4716 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20
  = du_fs'8321'_4716 v1 v8 v14 v15 v16
du_fs'8321'_4716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_4716 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_4742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_4742 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.keeps-alloc
d_keeps'45'alloc_4746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_4746 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_4750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_4750 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid'
d_valid''_4756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
d_valid''_4756 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
               v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_valid''_4756 v0 v1 v2 v3 v8 v13 v14 v15 v16 v23
du_valid''_4756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
du_valid''_4756 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
      (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_fs'8321'_4716 (coe v1) (coe v4) (coe v6) (coe v7) (coe v8)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-ptr
d_out'45'ptr_4770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'ptr_4770 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_4778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_4778 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.before'
d_before''_4786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before''_4786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_before''_4786 v22
du_before''_4786 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before''_4786 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.place
d_place_4792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_4792 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 v13
             v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_place_4792 v0 v1 v2 v3 v8 v13 v14 v15 v16 v21
du_place_4792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
du_place_4792 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3574 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1072
             v10
             (coe
                du_valid''''_4808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
             (coe
                du_valid''''_4808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'reg_3578 v10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1088
             v10
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3580
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1056
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.valid''
d_valid''''_4808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
d_valid''''_4808 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
                 v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
                 v27
  = du_valid''''_4808 v0 v1 v2 v3 v8 v13 v14 v15 v16 v27
du_valid''''_4808 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
du_valid''''_4808 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_valid''_4756 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-terminal
d_obs'45'correct'45'terminal_4824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'terminal_4824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  v8 ~v9 ~v10 ~v11 v12 ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20
  = du_obs'45'correct'45'terminal_4824 v8 v12 v14 v15 v16
du_obs'45'correct'45'terminal_4824 ::
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'terminal_4824 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
         (0 :: Integer)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
            (coe v3) (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         v1 v3
         (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336)
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1056))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_4886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_4886 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-initial
d_obs'45'correct'45'initial_4892 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'initial_4892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_obs'45'correct'45'initial_4892
du_obs'45'correct'45'initial_4892 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'initial_4892 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-free-heap
d_obs'45'correct'45'free'45'heap_4910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'free'45'heap_4910 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8 ~v9 ~v10 v11 v12 ~v13 v14 v15 v16 ~v17 v18 ~v19 ~v20
  = du_obs'45'correct'45'free'45'heap_4910
      v1 v8 v11 v12 v14 v15 v16 v18
du_obs'45'correct'45'free'45'heap_4910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'free'45'heap_4910 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
         (1 :: Integer)
         (coe du_fs'8321'_4946 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6))
         v3
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               du_fs'8321'_4946 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
               (coe
                  v2 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
         (coe
            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1056))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_4946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_4946 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20
  = du_fs'8321'_4946 v1 v8 v14 v15 v16
du_fs'8321'_4946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_4946 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_4972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_4972 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-fst
d_obs'45'correct'45'fst_4980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'fst_4980 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                             ~v10 ~v11 ~v12 v13 v14 v15 v16 v17 ~v18 ~v19 v20 ~v21
  = du_obs'45'correct'45'fst_4980
      v0 v1 v2 v3 v9 v13 v14 v15 v16 v17 v20
du_obs'45'correct'45'fst_4980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'fst_4980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_mr'45'of_5032 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5018 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_5018 v1 v9 v15 v16 v17
du_fs'8321'_5018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5018 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5022 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5028 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mr-of
d_mr'45'of_5032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_mr'45'of_5032 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
                v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_mr'45'of_5032 v0 v1 v2 v3 v9 v13 v14 v15 v16 v17 v22
du_mr'45'of_5032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_mr'45'of_5032 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3574 v11 v12 v13
        -> coe
             du_go_5046 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) erased
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1912
                (coe
                   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1932
                   (coe v12)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.go
d_go_5046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_go_5046 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 v12 v13 v14
          v15 v16 v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_go_5046 v0 v1 v2 v3 v9 v12 v13 v14 v15 v16 v17 v19 v26
du_go_5046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_go_5046 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_788 v16 v18 v20 v21
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v18
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1072
                          v16
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v22) (coe v8)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                (coe
                                   du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                             (coe v21))
                          v20
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v22) (coe v8)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                (coe
                                   du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                             (coe v21))
                          v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_800 v17
        -> case coe v17 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v19
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1088
                          v19))
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v20
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5018 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1056))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-snd
d_obs'45'correct'45'snd_5080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'snd_5080 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9
                             ~v10 ~v11 ~v12 v13 v14 v15 v16 v17 ~v18 ~v19 v20 ~v21
  = du_obs'45'correct'45'snd_5080
      v0 v1 v2 v4 v9 v13 v14 v15 v16 v17 v20
du_obs'45'correct'45'snd_5080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'snd_5080 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_mr'45'of_5132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5118 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_5118 v1 v9 v15 v16 v17
du_fs'8321'_5118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5122 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5128 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mr-of
d_mr'45'of_5132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_mr'45'of_5132 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
                v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_mr'45'of_5132 v0 v1 v2 v4 v9 v13 v14 v15 v16 v17 v22
du_mr'45'of_5132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_mr'45'of_5132 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3574 v11 v12 v13
        -> coe
             du_go_5146 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) erased
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1914
                (coe
                   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1932
                   (coe v12)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.go
d_go_5146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_go_5146 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 v12 v13 v14
          v15 v16 v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_go_5146 v0 v1 v2 v4 v9 v12 v13 v14 v15 v16 v17 v19 v26
du_go_5146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_go_5146 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_788 v16 v18 v20 v21
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v18
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1072
                          v16
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v23) (coe v8)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                (coe
                                   du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                             (coe v21))
                          v20
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
                             (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v23) (coe v8)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                (coe
                                   du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                             (coe v21))
                          v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_800 v17
        -> case coe v17 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v19
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1088
                          v19))
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v20
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5118 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1056))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-out-μ
d_obs'45'correct'45'out'45'μ_5180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'out'45'μ_5180 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                  v9 ~v10 ~v11 v12 v13 v14 v15 v16 v17 ~v18 v19 v20 ~v21
  = du_obs'45'correct'45'out'45'μ_5180
      v0 v1 v2 v3 v9 v12 v13 v14 v15 v16 v17 v19 v20
du_obs'45'correct'45'out'45'μ_5180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'out'45'μ_5180 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
         (1 :: Integer)
         (coe
            du_fs'8321'_5220 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10))
         v6
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               du_fs'8321'_5220 (coe v1) (coe v4) (coe v8) (coe v9) (coe v10)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
               (coe
                  v5 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
         (coe
            du_place_5300 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)
            (coe v8) (coe v9) (coe v10) (coe v12)))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.regs'
d_regs''_5218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs''_5218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_regs''_5218 v15
du_regs''_5218 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_regs''_5218 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5220 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_5220 v1 v9 v15 v16 v17
du_fs'8321'_5220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5220 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_776
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5246 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.keeps-alloc
d_keeps'45'alloc_5250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_5250 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5254 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid'
d_valid''_5260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
d_valid''_5260 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
               ~v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_valid''_5260 v0 v1 v2 v3 v9 v14 v15 v16 v17 v24
du_valid''_5260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
du_valid''_5260 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5728
      (coe v0) (coe v1) (coe v2) (coe v7)
      (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v3)) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_fs'8321'_5220 (coe v1) (coe v4) (coe v6) (coe v7) (coe v8)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid''
d_valid''''_5274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
d_valid''''_5274 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
                 ~v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_valid''''_5274 v0 v1 v2 v3 v9 v14 v15 v16 v17 v24
du_valid''''_5274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590
du_valid''''_5274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_3308
      (coe
         du_valid''_5260 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-ptr
d_out'45'ptr_5286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'ptr_5286 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.before'
d_before''_5294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before''_5294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_before''_5294 v23
du_before''_5294 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before''_5294 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.place
d_place_5300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
d_place_5300 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
             v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_place_5300 v0 v1 v2 v3 v9 v14 v15 v16 v17 v22
du_place_5300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_620
du_place_5300 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3574 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1072
             v10
             (coe
                du_valid''''_5274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
             (coe
                du_valid''''_5274 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-const
d_obs'45'correct'45'const_5316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
d_obs'45'correct'45'const_5316 ~v0 v1 ~v2 ~v3 v4
  = du_obs'45'correct'45'const_5316 v1 v4
du_obs'45'correct'45'const_5316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3514
du_obs'45'correct'45'const_5316 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_528
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
                v19 ->
                coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                     (1 :: Integer)
                     (coe
                        du_fs'8321'_5354 (coe v0) (coe v2) (coe v6) (coe v7) (coe v13)
                        (coe v14) (coe v15))
                     v11
                     (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                        (coe
                           du_fs'8321'_5354 (coe v0) (coe v2) (coe v6) (coe v7) (coe v13)
                           (coe v14) (coe v15)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
                           (coe MAlonzo.Code.Once.Type.C_Int_132)
                           (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                           (coe
                              v10 (0 :: Integer)
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
                                 (coe MAlonzo.Code.Once.Type.C_Int_132)
                                 (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe v2))
                              erased))
                        (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1088
                        v1)))
      MAlonzo.Code.Once.IRTy.C_fits'45'float_530
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
                v19 ->
                coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3548
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3488
                     (1 :: Integer)
                     (coe
                        du_fs'8321'_5424 (coe v0) (coe v2) (coe v6) (coe v7) (coe v13)
                        (coe v14) (coe v15))
                     v11
                     (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                        (coe
                           du_fs'8321'_5424 (coe v0) (coe v2) (coe v6) (coe v7) (coe v13)
                           (coe v14) (coe v15)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__346
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
                           (coe MAlonzo.Code.Once.Type.C_Float_134)
                           (coe MAlonzo.Code.Once.Type.C_fits'45'float_196) (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                           (coe
                              v10 (0 :: Integer)
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
                                 (coe MAlonzo.Code.Once.Type.C_Float_134)
                                 (coe MAlonzo.Code.Once.Type.C_fits'45'float_196) (coe v2))
                              erased))
                        (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_336))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1088
                        v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.instr
d_instr_5352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_instr_5352 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_instr_5352 v3
du_instr_5352 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_instr_5352 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5354 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
                ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20
  = du_fs'8321'_5354 v1 v3 v7 v8 v14 v15 v16
du_fs'8321'_5354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5354 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330 v0
      (coe du_instr_5352 (coe v1)) v2
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5380 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_5386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_5386 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.instr
d_instr_5422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_instr_5422 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_instr_5422 v3
du_instr_5422 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_instr_5422 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Type.C_fits'45'float_196) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5424 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
                ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20
  = du_fs'8321'_5424 v1 v3 v7 v8 v14 v15 v16
du_fs'8321'_5424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5424 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330 v0
      (coe du_instr_5422 (coe v1)) v2
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5450 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_5456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3560 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_5456 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-In
d_obs'45'correct'45'In_5462
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-In"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-pair
d_obs'45'correct'45'pair_5474
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-pair"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-case
d_obs'45'correct'45'case_5486
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-case"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Para
d_obs'45'correct'45'Para_5496
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Para"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-in-ν
d_obs'45'correct'45'in'45'ν_5502
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-in-\957"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Hylo
d_obs'45'correct'45'Hylo_5518
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Hylo"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Fuse
d_obs'45'correct'45'Fuse_5534
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-Fuse"
