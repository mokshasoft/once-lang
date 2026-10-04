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

module MAlonzo.Code.Once.CCC.Machine.FlatStackPtr where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatStackPtr._.readLoc
d_readLoc_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_26 ~v0 = du_readLoc_26
du_readLoc_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_26
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.FlatStackPtr._.writeHeapMem-aux
d_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_32 ~v0 = du_writeHeapMem'45'aux_32
du_writeHeapMem'45'aux_32 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_786 v2
      v3 v4
-- Once.CCC.Machine.FlatStackPtr._.writeLoc
d_writeLoc_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_34 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.writeLocToHeap
d_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_50 ~v0 = du_writeLocToHeap_50
du_writeLocToHeap_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_50
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_812
-- Once.CCC.Machine.FlatStackPtr._.writeLocToStack
d_writeLocToStack_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_802 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.writeStackMem-aux
d_writeStackMem'45'aux_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeStackMem'45'aux_56 ~v0 = du_writeStackMem'45'aux_56
du_writeStackMem'45'aux_56 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem'45'aux_56 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_674 v4
      v5 v6 v7
-- Once.CCC.Machine.FlatStackPtr._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_68 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_68
du_exec'45'load'45'suc'45'via'45'resolved_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_68
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1512
-- Once.CCC.Machine.FlatStackPtr._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'via'45'resolved_70 ~v0
  = du_exec'45'load'45'via'45'resolved_70
du_exec'45'load'45'via'45'resolved_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'via'45'resolved_70
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1474
-- Once.CCC.Machine.FlatStackPtr._.exec-load-with-value
d_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'with'45'value_72 ~v0
  = du_exec'45'load'45'with'45'value_72
du_exec'45'load'45'with'45'value_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'with'45'value_72
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'with'45'value_1462
-- Once.CCC.Machine.FlatStackPtr._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1524
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'via'45'resolved_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1486
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.call-sigop-ans
d_call'45'sigop'45'ans_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans_2940
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans'45'at_90 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans'45'at_2910
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.call-sigop-val
d_call'45'sigop'45'val_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'val_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2974
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.exec-abstract
d_exec'45'abstract_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_116 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_116
du_exec'45'load'45'from'45'slot'45'with'45'value_116 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_116
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2636
-- Once.CCC.Machine.FlatStackPtr._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_126 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_126
du_exec'45'restore'45'input'45'with'45'value_126 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_126
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2648
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output
d_exec'45'sigop'45'output_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3110
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.res-sv
d_res'45'sv_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_res'45'sv_192 ~v0 = du_res'45'sv_192
du_res'45'sv_192 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_res'45'sv_192
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_res'45'sv_3012
-- Once.CCC.Machine.FlatStackPtr._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_198 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2864
      v0
-- Once.CCC.Machine.FlatStackPtr._.CallPost
d_CallPost_204 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatStackPtr._.FlatState
d_FlatState_206 a0 = ()
-- Once.CCC.Machine.FlatStackPtr._.do-branch
d_do'45'branch_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_226 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.do-call
d_do'45'call_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_230 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.do-call-at
d_do'45'call'45'at_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_232 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.do-jump
d_do'45'jump_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'jump_244 ~v0 = du_do'45'jump_244
du_do'45'jump_244 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'jump_244
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'jump_922
-- Once.CCC.Machine.FlatStackPtr._.do-ret
d_do'45'ret_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_246 ~v0 = du_do'45'ret_246
du_do'45'ret_246 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_246
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_1140
-- Once.CCC.Machine.FlatStackPtr._.do-thunk
d_do'45'thunk_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_260 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.flat-exec-instr
d_flat'45'exec'45'instr_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_338 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.falloc
d_falloc_498 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_498 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fclosure
d_fclosure_500 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_500 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.flink
d_flink_502 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_502 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.floc
d_floc_504 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_504 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fpc
d_fpc_506 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_506 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatStackPtr._.FlatState.fret
d_fret_508 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_508 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK
d_StackPtrOK_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_StackPtrOK_522 = erased
-- Once.CCC.Machine.FlatStackPtr.StackPtrOK?
d_StackPtrOK'63'_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_StackPtrOK'63'_528 = erased
-- Once.CCC.Machine.FlatStackPtr.SPInv
d_SPInv_534 a0 a1 = ()
data T_SPInv_534
  = C_mkStackPtrWF_566 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                        AgdaAny)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                       (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-regs
d_sp'45'regs_554 ::
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_sp'45'regs_554 v0
  = case coe v0 of
      C_mkStackPtrWF_566 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-heap
d_sp'45'heap_558 ::
  T_SPInv_534 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_sp'45'heap_558 v0
  = case coe v0 of
      C_mkStackPtrWF_566 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.SPInv.sp-stack
d_sp'45'stack_564 :: T_SPInv_534 -> AgdaAny -> Integer -> AgdaAny
d_sp'45'stack_564 v0
  = case coe v0 of
      C_mkStackPtrWF_566 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.StackPtrWF
d_StackPtrWF_568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_StackPtrWF_568 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-frame
d_stack'45'ptr'45'frame_580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_534 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'ptr'45'frame_580 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-suc-live
d_stack'45'ptr'45'suc'45'live_602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_534 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'ptr'45'suc'45'live_602 = erased
-- Once.CCC.Machine.FlatStackPtr.stack-ptr-live
d_stack'45'ptr'45'live_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny ->
  Integer ->
  T_SPInv_534 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'ptr'45'live_624 = erased
-- Once.CCC.Machine.FlatStackPtr.readReg-write
d_readReg'45'write_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readReg'45'write_646 ~v0 ~v1 v2 v3 ~v4
  = du_readReg'45'write_646 v2 v3
du_readReg'45'write_646 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readReg'45'write_646 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-halt
d_sp'45'halt_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool -> T_SPInv_534 -> T_SPInv_534
d_sp'45'halt_718 ~v0 ~v1 ~v2 ~v3 v4 = du_sp'45'halt_718 v4
du_sp'45'halt_718 :: T_SPInv_534 -> T_SPInv_534
du_sp'45'halt_718 v0 = coe v0
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg
d_sp'45'write'45'reg_736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'write'45'reg_736 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'reg_736 v3 v5 v6
du_sp'45'write'45'reg_736 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'write'45'reg_736 v0 v1 v2
  = coe
      C_mkStackPtrWF_566
      (coe
         (\ v3 ->
            coe
              du_go_756 (coe v1) (coe v2) (coe v3)
              (coe du_readReg'45'write_646 (coe v0) (coe v3))))
      (coe d_sp'45'heap_558 (coe v2)) (coe d_sp'45'stack_564 (coe v2))
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_756 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_756 v5 v6 v7 v8
du_go_756 ::
  AgdaAny ->
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_756 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_sp'45'regs_554 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-reg-halt
d_sp'45'write'45'reg'45'halt_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'write'45'reg'45'halt_794 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_sp'45'write'45'reg'45'halt_794 v3 v7 v8
du_sp'45'write'45'reg'45'halt_794 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'write'45'reg'45'halt_794 v0 v1 v2
  = coe du_sp'45'write'45'reg_736 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatStackPtr.sp-wsm-aux
d_sp'45'wsm'45'aux_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_sp'45'wsm'45'aux_830 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 v10
  = du_sp'45'wsm'45'aux_830 v5 v6 v9 v10
du_sp'45'wsm'45'aux_830 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'wsm'45'aux_830 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe seq (coe v7) (coe v3)
                              else coe seq (coe v7) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-whm-aux
d_sp'45'whm'45'aux_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_sp'45'whm'45'aux_866 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_sp'45'whm'45'aux_866 v3 v6 v7
du_sp'45'whm'45'aux_866 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sp'45'whm'45'aux_866 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-write-stack
d_sp'45'write'45'stack_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'write'45'stack_894 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_sp'45'write'45'stack_894 v0 v3 v4 v6 v7
du_sp'45'write'45'stack_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'write'45'stack_894 v0 v1 v2 v3 v4
  = coe
      C_mkStackPtrWF_566 (coe d_sp'45'regs_554 (coe v4))
      (coe d_sp'45'heap_558 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_sp'45'wsm'45'aux_830
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_sp'45'stack_564 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatStackPtr.sp-write-heap
d_sp'45'write'45'heap_922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'write'45'heap_922 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'heap_922 v3 v5 v6
du_sp'45'write'45'heap_922 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'write'45'heap_922 v0 v1 v2
  = coe
      C_mkStackPtrWF_566 (coe d_sp'45'regs_554 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_sp'45'whm'45'aux_866
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_sp'45'heap_558 v2 v3) (coe v1)))
      (coe d_sp'45'stack_564 (coe v2))
-- Once.CCC.Machine.FlatStackPtr.writeLoc-dyn
d_writeLoc'45'dyn_944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'dyn_944 = erased
-- Once.CCC.Machine.FlatStackPtr.sp-write-mem
d_sp'45'write'45'mem_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'write'45'mem_988 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'write'45'mem_988 v0 v3 v5 v6
du_sp'45'write'45'mem_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'write'45'mem_988 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_sp'45'write'45'stack_894 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_sp'45'write'45'heap_922 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-read-loc
d_sp'45'read'45'loc_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_sp'45'read'45'loc_1022 ~v0 ~v1 ~v2 v3 v4
  = du_sp'45'read'45'loc_1022 v3 v4
du_sp'45'read'45'loc_1022 ::
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_sp'45'read'45'loc_1022 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_sp'45'stack_564 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_sp'45'heap_558 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-value
d_sp'45'load'45'value_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'load'45'value_1050 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_sp'45'load'45'value_1050 v3 v4 v5 v6
du_sp'45'load'45'value_1050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'load'45'value_1050 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_sp'45'write'45'reg_736 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-resolved
d_sp'45'load'45'resolved_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'load'45'resolved_1082 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'resolved_1082 v2 v3 v4 v5
du_sp'45'load'45'resolved_1082 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_534 -> T_SPInv_534
du_sp'45'load'45'resolved_1082 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_1050 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v0)
                (coe v4))
             (coe du_sp'45'read'45'loc_1022 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-load-suc-resolved
d_sp'45'load'45'suc'45'resolved_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'load'45'suc'45'resolved_1110 ~v0 ~v1 v2 v3 v4 v5
  = du_sp'45'load'45'suc'45'resolved_1110 v2 v3 v4 v5
du_sp'45'load'45'suc'45'resolved_1110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_SPInv_534 -> T_SPInv_534
du_sp'45'load'45'suc'45'resolved_1110 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'load'45'value_1050 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe
                du_sp'45'read'45'loc_1022 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-resolved
d_sp'45'store'45'resolved_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'store'45'resolved_1138 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'resolved_1138 v0 v3 v5 v6
du_sp'45'store'45'resolved_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'store'45'resolved_1138 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_988 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-store-suc-resolved
d_sp'45'store'45'suc'45'resolved_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'store'45'suc'45'resolved_1170 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_sp'45'store'45'suc'45'resolved_1170 v0 v3 v5 v6
du_sp'45'store'45'suc'45'resolved_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'store'45'suc'45'resolved_1170 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_sp'45'write'45'mem_988 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-from-slot
d_sp'45'from'45'slot_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'from'45'slot_1200 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'from'45'slot_1200 v3 v4 v5
du_sp'45'from'45'slot_1200 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'from'45'slot_1200 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-restore
d_sp'45'restore_1226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'restore_1226 ~v0 ~v1 ~v2 v3 v4 v5
  = du_sp'45'restore_1226 v3 v4 v5
du_sp'45'restore_1226 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
du_sp'45'restore_1226 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-pred
d_sp'45'pred_1248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sp'45'pred_1248 ~v0 v1 = du_sp'45'pred_1248 v1
du_sp'45'pred_1248 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sp'45'pred_1248 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-succ
d_sp'45'succ_1262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_sp'45'succ_1262 ~v0 v1 = du_sp'45'succ_1262 v1
du_sp'45'succ_1262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_sp'45'succ_1262 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr.sp-reg-op
d_sp'45'reg'45'op_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'reg'45'op_1280 ~v0 ~v1 v2 v3 v4
  = du_sp'45'reg'45'op_1280 v2 v3 v4
du_sp'45'reg'45'op_1280 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  T_SPInv_534 -> T_SPInv_534
du_sp'45'reg'45'op_1280 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe
                du_sp'45'pred_1248
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe
                d_sp'45'regs_554 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)
             (coe
                du_sp'45'succ_1262
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack
d_structured'45'pure'45'sigop'45'no'45'stack_1326
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatStackPtr.structured-pure-sigop-no-stack"
-- Once.CCC.Machine.FlatStackPtr.res-sv-stack-ok
d_res'45'sv'45'stack'45'ok_1334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
d_res'45'sv'45'stack'45'ok_1334 ~v0 ~v1 ~v2 v3
  = du_res'45'sv'45'stack'45'ok_1334 v3
du_res'45'sv'45'stack'45'ok_1334 ::
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_res'45'sv'45'stack'45'ok_1334 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr.sigop-output-ok
d_sigop'45'output'45'ok_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> AgdaAny
d_sigop'45'output'45'ok_1350 v0 v1 v2 v3 v4
  = coe
      d_go_1390 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v3))
-- Once.CCC.Machine.FlatStackPtr._.pov
d_pov_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> Maybe AgdaAny -> AgdaAny
d_pov_1368 v0 v1 v2 v3 ~v4 ~v5 v6 = du_pov_1368 v0 v1 v2 v3 v6
du_pov_1368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny -> AgdaAny
du_pov_1368 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_res'45'sv'45'stack'45'ok_1334
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_342 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_162 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166
                   (coe v0))
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._.aux
d_aux_1380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1380 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pov_1368 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818 (coe v1)
                       (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1368 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2762
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v4))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'no'45'stack_1326 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_1390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 -> AgdaAny
d_go_1390 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe
             d_aux_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v2))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v4))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe
             d_cv_1398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._._.cv
d_cv_1398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny
d_cv_1398 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_ans_1408 (coe v1) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'dec_2962
                (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._._._.ans
d_ans_1408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_ans_1408 ~v0 v1 ~v2 v3 v4 ~v5 v6 = du_ans_1408 v1 v3 v4 v6
du_ans_1408 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_ans_1408 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_at_1418
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2868 (coe v0)
                          (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                          (coe v2)))
             else coe seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr._._._._.at
d_at_1418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> AgdaAny
d_at_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_at_1418 v7
du_at_1418 :: Maybe AgdaAny -> AgdaAny
du_at_1418 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatStackPtr.sp-abstract
d_sp'45'abstract_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_sp'45'abstract_1426 v0 v1 v2 v3 ~v4 v5
  = du_sp'45'abstract_1426 v0 v1 v2 v3 v5
du_sp'45'abstract_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_SPInv_534 -> T_SPInv_534
du_sp'45'abstract_1426 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe
             du_sp'45'load'45'resolved_1082 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe
             du_sp'45'load'45'suc'45'resolved_1110 (coe v2)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v5
        -> coe
             du_sp'45'from'45'slot_1200
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_1022 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v5
        -> coe
             du_sp'45'write'45'mem_988 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v3))
                (coe v5))
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe
             du_sp'45'store'45'resolved_1138 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe
             du_sp'45'store'45'suc'45'resolved_1170 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v5
        -> coe
             du_sp'45'restore_1226
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_1022 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v5
        -> coe
             du_sp'45'write'45'mem_988 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v3))
                (coe v5))
             (coe
                d_sp'45'regs_554 v4
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v5
        -> coe
             du_sp'45'from'45'slot_1200
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe
                du_sp'45'read'45'loc_1022 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe v3))
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v5
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v5 v6 v7
        -> coe
             du_sp'45'write'45'reg'45'halt_794
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                d_sigop'45'output'45'ok_1350 (coe v0) (coe v5) (coe v6) (coe v7)
                (coe v2))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v5 v6 v7
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v5
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe v4
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v5
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v5
        -> coe
             du_sp'45'write'45'reg_736
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v5
        -> coe du_sp'45'reg'45'op_1280 (coe v2) (coe v5) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatStackPtr.sp-jump
d_sp'45'jump_1712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'jump_1712 ~v0 v1 ~v2 v3 = du_sp'45'jump_1712 v1 v3
du_sp'45'jump_1712 :: Maybe Integer -> T_SPInv_534 -> T_SPInv_534
du_sp'45'jump_1712 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.sp-branch
d_sp'45'branch_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'branch_1732 v0 v1 v2 v3 ~v4 v5
  = du_sp'45'branch_1732 v0 v1 v2 v3 v5
du_sp'45'branch_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_SPInv_534 -> T_SPInv_534
du_sp'45'branch_1732 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_sp'45'jump_1712
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatStackPtr.sp-ret
d_sp'45'ret_1754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'ret_1754 ~v0 v1 ~v2 v3 = du_sp'45'ret_1754 v1 v3
du_sp'45'ret_1754 :: [Integer] -> T_SPInv_534 -> T_SPInv_534
du_sp'45'ret_1754 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.sp-thunk
d_sp'45'thunk_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'thunk_1772 v0 v1 v2 v3
  = coe
      C_mkStackPtrWF_566 (coe d_sp'45'regs_554 (coe v3))
      (coe d_sp'45'heap_558 (coe v3))
      (coe d_cleared_1788 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatStackPtr._.cleared
d_cleared_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> AgdaAny -> Integer -> AgdaAny
d_cleared_1788 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 v0
              (coe
                 MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_108 v0
                 (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
                 v1)
              v4 in
    coe
      (let v7
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 (\ v7 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                      (coe addInt (coe (1 :: Integer)) (coe v5)))
                 (coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v1))) in
       coe
         (case coe v6 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
              -> if coe v8
                   then coe
                          seq (coe v9)
                          (case coe v7 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                               -> if coe v10
                                    then coe
                                           seq (coe v11) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    else coe seq (coe v11) (coe d_sp'45'stack_564 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_sp'45'stack_564 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatStackPtr.sp-call
d_sp'45'call_1814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'call_1814 v0 v1 v2 v3
  = coe
      du_go_1826 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
         (coe v1) (coe v2))
-- Once.CCC.Machine.FlatStackPtr._.go
d_go_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_SPInv_534
d_go_1826 ~v0 ~v1 ~v2 v3 v4 = du_go_1826 v3 v4
du_go_1826 ::
  T_SPInv_534 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_SPInv_534
du_go_1826 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatStackPtr.sp-call-at
d_sp'45'call'45'at_1850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
d_sp'45'call'45'at_1850 ~v0 v1 ~v2 v3
  = du_sp'45'call'45'at_1850 v1 v3
du_sp'45'call'45'at_1850 ::
  Maybe Integer -> T_SPInv_534 -> T_SPInv_534
du_sp'45'call'45'at_1850 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatStackPtr.flat-stack-ptr
d_flat'45'stack'45'ptr_1868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> T_SPInv_534 -> T_SPInv_534
d_flat'45'stack'45'ptr_1868 v0 v1 v2 v3 ~v4 v5
  = du_flat'45'stack'45'ptr_1868 v0 v1 v2 v3 v5
du_flat'45'stack'45'ptr_1868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_SPInv_534 -> T_SPInv_534
du_flat'45'stack'45'ptr_1868 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe d_sp'45'call_1814 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v5 v6 v7
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v5 v6 v7
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v5
        -> coe
             du_sp'45'abstract_1426 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
             (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216 v6 -> coe v4
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218 v6
               -> coe
                    du_sp'45'jump_1712
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220 v6
               -> coe
                    du_sp'45'branch_1732 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222 v6
               -> coe
                    du_sp'45'branch_1732 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v6) (coe v2) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224 v6 v7
               -> coe d_sp'45'thunk_1772 (coe v0) (coe v7) (coe v3) (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226 v6
               -> coe
                    du_sp'45'ret_1754
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2228 v6
               -> coe
                    du_sp'45'call'45'at_1850
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
                       (coe v2) (coe v6))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2230 v6
               -> coe d_sp'45'thunk_1772 (coe v0) (coe v6) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
