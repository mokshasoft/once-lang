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
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
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
d_Σ_11 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.AbstractReg
d_AbstractReg_13 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.⊤
d_'8868'_19 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.BeforeFrontier
d_BeforeFrontier_732 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.CellAt
d_CellAt_750 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.FlatSteps
d_FlatSteps_760 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.IRObsCorrectF
d_IRObsCorrectF_772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_772 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.InputAt
d_InputAt_776 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF
d_MachineRefinesObsF_782 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ResultPlace
d_ResultPlace_790 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValidAtWF
d_ValidAtWF_800 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized
d_ValueRealized_802 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                    a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.evalᴰ
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.prim-sv
d_prim'45'sv_1130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_1130 ~v0 ~v1 ~v2 = du_prim'45'sv_1130
du_prim'45'sv_1130 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_1130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.readLoc
d_readLoc_1152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1152 ~v0 ~v1 ~v2 = du_readLoc_1152
du_readLoc_1152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1152
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF.traces-agree
d_traces'45'agree_1416 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_1416 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.MachineRefinesObsF.value-realized
d_value'45'realized_1418 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_1418 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.at-end
d_at'45'end_1480 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_1480 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.bf-mono
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.cont-alloc
d_cont'45'alloc_1484 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_1484 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.frame-pres
d_frame'45'pres_1486 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_1486 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.heap-pres
d_heap'45'pres_1488 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_1488 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.live
d_live_1490 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_1490 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.log
d_log_1492 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_1492 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.no-link
d_no'45'link_1494 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_1494 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.no-ret
d_no'45'ret_1496 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_1496 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.out-mode
d_out'45'mode_1498 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_1498 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.place
d_place_1500 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_1500 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.run
d_run_1502 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_1502 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.settle
d_settle_1504 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_1504 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.stack-pres
d_stack'45'pres_1506 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_1506 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.steps
d_steps_1508 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_1508 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Core.ValueRealized.stops
d_stops_1510 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_1510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_1514 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._._≡_
d__'8801'__2026 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.AbstractInstr
d_AbstractInstr_2052 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal
d_Decimal_2076 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FitsInReg
d_FitsInReg_2084 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FitsInRegI
d_FitsInRegI_2086 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics
d_FrameSemantics_2088 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.IR
d_IR_2104 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.IRTy
d_IRTy_2106 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.List
d_List_2118 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.StoredValue
d_StoredValue_2152 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.ValueLocation
d_ValueLocation_2160 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.WellFormedFI
d_WellFormedFI_2162 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.fst
d_fst_2278 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_fst_2278 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.snd
d_snd_2280 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_snd_2280 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.readReg
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.sucLoc
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Int
d_Int_2342 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple._.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_2362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_2362 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.⟦_⟧TI
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal.exp10
d_exp10_2614 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_exp10_2614 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_exp10_14 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.Decimal.sig
d_sig_2616 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 -> Integer
d_sig_2616 v0
  = coe MAlonzo.Code.Once.Float.Decimal.d_sig_12 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics._≟F_
d__'8799'F__3088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__3088 v0
  = coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics._≺_
d__'8826'__3090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> ()
d__'8826'__3090 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.Frame
d_Frame_3092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_3092 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.float-format
d_float'45'format_3094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_3094 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-base
d_frame'45'base_3096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
d_frame'45'base_3096 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_92 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-disjoint-bounded
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-word
d_frame'45'word_3100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_frame'45'word_3100 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.frame-word-pos
d_frame'45'word'45'pos_3102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'word'45'pos_3102 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word'45'pos_112
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.fs-interp
d_fs'45'interp_3104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_fs'45'interp_3104 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.shift-base
d_shift'45'base_3106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_3106 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.shift-frame
d_shift'45'frame_3108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_3108 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-addr
d_slot'45'addr_3110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
d_slot'45'addr_3110 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_94 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-addr-linear
d_slot'45'addr'45'linear_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_3112 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-injective
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
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.slot-zero-at-base
d_slot'45'zero'45'at'45'base_3116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_3116 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-compare
d_'8826''45'compare_3118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_3118 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'compare_148
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-irrefl
d_'8826''45'irrefl_3120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_3120 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple._.FrameSemantics.≺-trans
d_'8826''45'trans_3122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8826''45'trans_3122 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.BeforeFrontier
d_BeforeFrontier_3826 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.CellAt
d_CellAt_3844 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.FlatSteps
d_FlatSteps_3854 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.IRObsCorrectF
d_IRObsCorrectF_3866 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_3866 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.InputAt
d_InputAt_3870 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF
d_MachineRefinesObsF_3876 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                          a13 a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ResultPlace
d_ResultPlace_3884 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValidAtWF
d_ValidAtWF_3894 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized
d_ValueRealized_3896 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                     a14
  = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.evalᴰ
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
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.prim-sv
d_prim'45'sv_4224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_4224 ~v0 ~v1 ~v2 = du_prim'45'sv_4224
du_prim'45'sv_4224 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_4224 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_582
      v1 v2
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.readLoc
d_readLoc_4246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_4246 ~v0 ~v1 ~v2 = du_readLoc_4246
du_readLoc_4246 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_4246
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF.traces-agree
d_traces'45'agree_4510 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_traces'45'agree_4510 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.MachineRefinesObsF.value-realized
d_value'45'realized_4512 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602
d_value'45'realized_4512 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_value'45'realized_3816
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.at-end
d_at'45'end_4574 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'end_4574 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.bf-mono
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
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.cont-alloc
d_cont'45'alloc_4578 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_cont'45'alloc_4578 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_cont'45'alloc_3678
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.frame-pres
d_frame'45'pres_4580 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'pres_4580 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.heap-pres
d_heap'45'pres_4582 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'pres_4582 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.live
d_live_4584 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_live_4584 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.log
d_log_4586 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_log_4586 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.no-link
d_no'45'link_4588 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'link_4588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.no-ret
d_no'45'ret_4590 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'ret_4590 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.out-mode
d_out'45'mode_4592 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4
d_out'45'mode_4592 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_out'45'mode_3676
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.place
d_place_4594 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_4594 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_place_3696
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.run
d_run_4596 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_358
d_run_4596 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_run_3680
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.settle
d_settle_4598 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_4598 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_settle_3674
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.stack-pres
d_stack'45'pres_4600 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'pres_4600 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.steps
d_steps_4602 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  Integer
d_steps_4602 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.d_steps_3672
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.ValueRealized.stops
d_stops_4604 ::
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_ValueRealized_3602 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stops_4604 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_4608 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-id
d_obs'45'correct'45'id_5102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'id_5102 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
                            ~v11 ~v12 v13 v14 v15 v16 v17 ~v18 v19 v20 ~v21
  = du_obs'45'correct'45'id_5102
      v0 v1 v2 v3 v7 v10 v13 v14 v15 v16 v17 v19 v20
du_obs'45'correct'45'id_5102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'id_5102 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
         (1 :: Integer)
         (coe
            du_fs'8321'_5140 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
         v6
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               du_fs'8321'_5140 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
               (coe
                  v5 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
         (\ v13 v14 ->
            coe
              du_place_5216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)
              (coe v8) (coe v9) (coe v10) (coe v12))
         (\ v13 v14 v15 -> v15))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.regs'
d_regs''_5138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs''_5138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_regs''_5138 v15
du_regs''_5138 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_regs''_5138 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5140 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_5140 v2 v7 v15 v16 v17
du_fs'8321'_5140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5140 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5166 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.keeps-alloc
d_keeps'45'alloc_5170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_5170 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5174 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid'
d_valid''_5180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid''_5180 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_valid''_5180 v0 v1 v2 v3 v7 v14 v15 v16 v17 v24
du_valid''_5180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid''_5180 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_fs'8321'_5140 (coe v2) (coe v4) (coe v6) (coe v7) (coe v8)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-ptr
d_out'45'ptr_5194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'ptr_5194 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_5202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_5202 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.before'
d_before''_5210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_before''_5210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_before''_5210 v23
du_before''_5210 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_before''_5210 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.place
d_place_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5216 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
             v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_place_5216 v0 v1 v2 v3 v7 v14 v15 v16 v17 v22
du_place_5216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
du_place_5216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1076
             v10
             (coe
                du_valid''''_5232 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
             (coe
                du_valid''''_5232 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'reg_3850 v10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
             v10
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'unit_3852
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1060
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.valid''
d_valid''''_5232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid''''_5232 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                 ~v13 v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
                 ~v27 v28
  = du_valid''''_5232 v0 v1 v2 v3 v7 v14 v15 v16 v17 v28
du_valid''''_5232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid''''_5232 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_valid''_5180 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-terminal
d_obs'45'correct'45'terminal_5270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'terminal_5270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                  ~v8 ~v9 ~v10 ~v11 ~v12 v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_obs'45'correct'45'terminal_5270 v7 v13 v15 v16 v17
du_obs'45'correct'45'terminal_5270 ::
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'terminal_5270 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
         (0 :: Integer)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
            (coe v3) (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         v1 v3
         (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364)
         (\ v5 v6 ->
            coe
              MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1060)
         (\ v5 v6 v7 -> v7))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5332 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-initial
d_obs'45'correct'45'initial_5360 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'initial_5360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_obs'45'correct'45'initial_5360
du_obs'45'correct'45'initial_5360 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'initial_5360 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-fst
d_obs'45'correct'45'fst_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'fst_5380 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                             ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17 v18 ~v19 ~v20 v21 ~v22
  = du_obs'45'correct'45'fst_5380
      v0 v1 v2 v3 v8 v14 v15 v16 v17 v18 v21
du_obs'45'correct'45'fst_5380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'fst_5380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_mr'45'of_5432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5418 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_fs'8321'_5418 v2 v8 v16 v17 v18
du_fs'8321'_5418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5418 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5422 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5428 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5428 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mr-of
d_mr'45'of_5432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_mr'45'of_5432 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
                ~v13 v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_mr'45'of_5432 v0 v1 v2 v3 v8 v14 v15 v16 v17 v18 v23
du_mr'45'of_5432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_mr'45'of_5432 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846 v11 v12 v13
        -> coe
             du_go_5446 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) erased
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_fst'45'cell_1928
                (coe
                   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1948
                   (coe v12)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.go
d_go_5446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_go_5446 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 ~v12 ~v13 v14
          v15 v16 v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 v27
  = du_go_5446 v0 v1 v2 v3 v8 v11 v14 v15 v16 v17 v18 v20 v27
du_go_5446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_go_5446 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v16 v18 v20 v21
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v18
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v24 v25 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1076
                            v16
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
                               (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v22) (coe v8)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                  (coe
                                     du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9)
                                     (coe v10)))
                               (coe v21))
                            v20
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
                               (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v22) (coe v8)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                  (coe
                                     du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9)
                                     (coe v10)))
                               (coe v21))
                            v20)
                       (\ v24 v25 v26 -> v26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v17
        -> case coe v17 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_594 v19
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v20 v21 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
                            v19)
                       (\ v20 v21 v22 -> v22))
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_596 v20
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5418 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v21 v22 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1060)
                       (\ v21 v22 v23 -> v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-snd
d_obs'45'correct'45'snd_5546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'snd_5546 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9
                             ~v10 ~v11 ~v12 ~v13 v14 v15 v16 v17 v18 ~v19 ~v20 v21 ~v22
  = du_obs'45'correct'45'snd_5546
      v0 v1 v2 v4 v8 v14 v15 v16 v17 v18 v21
du_obs'45'correct'45'snd_5546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'snd_5546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_mr'45'of_5598 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5584 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_fs'8321'_5584 v2 v8 v16 v17 v18
du_fs'8321'_5584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5584 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5588 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5594 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mr-of
d_mr'45'of_5598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_mr'45'of_5598 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
                ~v13 v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_mr'45'of_5598 v0 v1 v2 v4 v8 v14 v15 v16 v17 v18 v23
du_mr'45'of_5598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_mr'45'of_5598 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846 v11 v12 v13
        -> coe
             du_go_5612 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) erased
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) erased
             (coe
                MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.d_snd'45'cell_1930
                (coe
                   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_decomposePairWF_1948
                   (coe v12)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._._.go
d_go_5612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_go_5612 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 ~v12 ~v13 v14
          v15 v16 v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 v27
  = du_go_5612 v0 v1 v2 v4 v8 v11 v14 v15 v16 v17 v18 v20 v27
du_go_5612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_612 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_go_5612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_816 v16 v18 v20 v21
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v18
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v24 v25 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1076
                            v16
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
                               (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v23) (coe v8)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                  (coe
                                     du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9)
                                     (coe v10)))
                               (coe v21))
                            v20
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
                               (coe v0) (coe v1) (coe v2) (coe v9) (coe v3) (coe v23) (coe v8)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
                                  (coe
                                     du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9)
                                     (coe v10)))
                               (coe v21))
                            v20)
                       (\ v24 v25 v26 -> v26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_828 v17
        -> case coe v17 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_594 v19
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v20 v21 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
                            v19)
                       (\ v20 v21 v22 -> v22))
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_596 v20
               -> coe
                    MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                    (coe
                       MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                       (1 :: Integer)
                       (coe
                          du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
                       v6
                       (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                          (coe
                             du_fs'8321'_5584 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                             (coe
                                v5 (0 :: Integer)
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                erased))
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                       (\ v21 v22 ->
                          coe
                            MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_unit'45'result_1060)
                       (\ v21 v22 v23 -> v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-out-μ
d_obs'45'correct'45'out'45'μ_5712 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'out'45'μ_5712 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8
                                  ~v9 ~v10 v11 ~v12 ~v13 v14 v15 v16 v17 v18 ~v19 v20 v21 ~v22
  = du_obs'45'correct'45'out'45'μ_5712
      v0 v1 v2 v3 v8 v11 v14 v15 v16 v17 v18 v20 v21
du_obs'45'correct'45'out'45'μ_5712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'out'45'μ_5712 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
         (1 :: Integer)
         (coe
            du_fs'8321'_5752 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10))
         v6
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
            (coe
               du_fs'8321'_5752 (coe v2) (coe v4) (coe v8) (coe v9) (coe v10)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
               (coe
                  v5 (0 :: Integer)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                  erased))
            (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
         (\ v13 v14 ->
            coe
              du_place_5832 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)
              (coe v8) (coe v9) (coe v10) (coe v12))
         (\ v13 v14 v15 -> v15))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.regs'
d_regs''_5750 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
d_regs''_5750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_regs''_5750 v16
du_regs''_5750 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124
du_regs''_5750 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5752 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5752 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_fs'8321'_5752 v2 v8 v16 v17 v18
du_fs'8321'_5752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5752 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_948
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v2)
         (coe v3) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5778 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5778 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.keeps-alloc
d_keeps'45'alloc_5782 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_5782 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.mem-eq
d_mem'45'eq_5786 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_5786 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid'
d_valid''_5792 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid''_5792 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_valid''_5792 v0 v1 v2 v3 v8 v15 v16 v17 v18 v25
du_valid''_5792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid''_5792 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_validityWF'45'mem'45'preserved_5192
      (coe v0) (coe v1) (coe v2) (coe v7)
      (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v3)) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82
         (coe
            du_fs'8321'_5752 (coe v2) (coe v4) (coe v6) (coe v7) (coe v8)))
      (coe v9)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.valid''
d_valid''''_5806 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
d_valid''''_5806 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
                 ~v13 ~v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_valid''''_5806 v0 v1 v2 v3 v8 v15 v16 v17 v18 v25
du_valid''''_5806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_616
du_valid''''_5806 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.du_μ'45'layer'45'iso_3448
      (coe
         du_valid''_5792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-ptr
d_out'45'ptr_5818 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'ptr_5818 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.before'
d_before''_5826 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_before''_5826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_before''_5826 v24
du_before''_5826 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_before''_5826 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.place
d_place_5832 ::
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
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
d_place_5832 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
             ~v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_place_5832 v0 v1 v2 v3 v8 v15 v16 v17 v18 v23
du_place_5832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  Integer ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ResultPlace_646
du_place_5832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_in'45'loc_3846 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'loc_1076
             v10
             (coe
                du_valid''''_5806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
             (coe
                du_valid''''_5806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
             v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-const
d_obs'45'correct'45'const_5870 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
d_obs'45'correct'45'const_5870 ~v0 ~v1 v2 ~v3 v4
  = du_obs'45'correct'45'const_5870 v2 v4
du_obs'45'correct'45'const_5870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_MachineRefinesObsF_3786
du_obs'45'correct'45'const_5870 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_520
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
                v20 ->
                coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                     (1 :: Integer)
                     (coe
                        du_fs'8321'_5908 (coe v0) (coe v2) (coe v5) (coe v6) (coe v14)
                        (coe v15) (coe v16))
                     v12
                     (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                        (coe
                           du_fs'8321'_5908 (coe v0) (coe v2) (coe v5) (coe v6) (coe v14)
                           (coe v15) (coe v16)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                           (coe MAlonzo.Code.Once.Type.C_Int_134)
                           (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                           (coe
                              v9 (0 :: Integer)
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                                 (coe MAlonzo.Code.Once.Type.C_Int_134)
                                 (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe v2))
                              erased))
                        (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                     (\ v21 v22 ->
                        coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
                          v1)
                     (\ v21 v22 v23 -> v23)))
      MAlonzo.Code.Once.IRTy.C_fits'45'float_522
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
                v20 ->
                coe
                  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_constructor_3820
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.C_realized_3716
                     (1 :: Integer)
                     (coe
                        du_fs'8321'_6000 (coe v0) (coe v2) (coe v5) (coe v6) (coe v14)
                        (coe v15) (coe v16))
                     v12
                     (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84
                        (coe
                           du_fs'8321'_6000 (coe v0) (coe v2) (coe v5) (coe v6) (coe v14)
                           (coe v15) (coe v16)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__374
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                           (coe MAlonzo.Code.Once.Type.C_Float_136)
                           (coe MAlonzo.Code.Once.Type.C_fits'45'float_204) (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                           (coe
                              v9 (0 :: Integer)
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                                 (coe MAlonzo.Code.Once.Type.C_Float_136)
                                 (coe MAlonzo.Code.Once.Type.C_fits'45'float_204) (coe v2))
                              erased))
                        (coe MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_364))
                     (\ v21 v22 ->
                        coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_1092
                          v1)
                     (\ v21 v22 v23 -> v23)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.instr
d_instr_5906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_instr_5906 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_instr_5906 v3
du_instr_5906 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_instr_5906 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
      (coe MAlonzo.Code.Once.Type.C_Int_134)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_5908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_5908 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_5908 v2 v3 v6 v7 v15 v16 v17
du_fs'8321'_5908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_5908 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v0
      (coe du_instr_5906 (coe v1)) v2
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_5934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_5934 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_5940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_5940 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.instr
d_instr_5998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_instr_5998 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_instr_5998 v3
du_instr_5998 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_instr_5998 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
      (coe MAlonzo.Code.Once.Type.C_Float_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'float_204) (coe v0)
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.fs₁
d_fs'8321'_6000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_fs'8321'_6000 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
                ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21
  = du_fs'8321'_6000 v2 v3 v6 v7 v15 v16 v17
du_fs'8321'_6000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_fs'8321'_6000 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502 v0
      (coe du_instr_5998 (coe v1)) v2
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94 (coe v4)
         (coe v5) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.denot-[]
d_denot'45''91''93'_6026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_6026 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp._.out-lit
d_out'45'lit_6032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
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
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.IRObsCorrect.Interface.T_InputAt_3832 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'lit_6032 = erased
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-In
d_obs'45'correct'45'In_6060
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-In"
-- Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-in-ν
d_obs'45'correct'45'in'45'ν_6066
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrect.Simple.Simp.obs-correct-in-\957"
