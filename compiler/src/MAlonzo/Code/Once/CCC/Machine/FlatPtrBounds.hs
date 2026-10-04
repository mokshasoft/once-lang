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

module MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds where

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
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackPtr
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.FlatPtrBounds._.readLoc
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
-- Once.CCC.Machine.FlatPtrBounds._.writeHeapMem-aux
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
-- Once.CCC.Machine.FlatPtrBounds._.writeLoc
d_writeLoc_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_34 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToHeap
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
-- Once.CCC.Machine.FlatPtrBounds._.writeLocToStack
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
-- Once.CCC.Machine.FlatPtrBounds._.writeStackMem-aux
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-suc-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-with-value
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-suc-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.exec-store-via-resolved
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
-- Once.CCC.Machine.FlatPtrBounds._.call-sigop-ans
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans_2932
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.call-sigop-ans-at
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans'45'at_2902
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.call-sigop-val
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2966
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-abstract
d_exec'45'abstract_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3220
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-load-from-slot-with-value
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2628
-- Once.CCC.Machine.FlatPtrBounds._.exec-restore-input-with-value
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2640
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output
d_exec'45'sigop'45'output_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3102
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.exec-sigop-output-of
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3060
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-aux
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3024
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.pure-sigop-out-val
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
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3000
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.res-sv
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
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_res'45'sv_3004
-- Once.CCC.Machine.FlatPtrBounds._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_198 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2856
      v0
-- Once.CCC.Machine.FlatPtrBounds._.CallPost
d_CallPost_204 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.FlatState
d_FlatState_206 a0 = ()
-- Once.CCC.Machine.FlatPtrBounds._.do-branch
d_do'45'branch_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'branch_226 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'branch_938 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-call
d_do'45'call_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call_230 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call_1340 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-call-at
d_do'45'call'45'at_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'call'45'at_232 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'call'45'at_1284 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.do-jump
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
-- Once.CCC.Machine.FlatPtrBounds._.do-ret
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
-- Once.CCC.Machine.FlatPtrBounds._.do-thunk
d_do'45'thunk_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_260 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1274 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.flat-exec-instr
d_flat'45'exec'45'instr_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_338 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.falloc
d_falloc_496 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_falloc_496 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fclosure
d_fclosure_498 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_498 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.flink
d_flink_500 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_500 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.floc
d_floc_502 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_502 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fpc
d_fpc_504 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_504 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.FlatState.fret
d_fret_506 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_506 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF
d_StoreWF_526 a0 a1 a2 = ()
-- Once.CCC.Machine.FlatPtrBounds._.sv-below
d_sv'45'below_530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_530 = erased
-- Once.CCC.Machine.FlatPtrBounds._.svm-below
d_svm'45'below_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_532 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-fresh
d_wf'45'fresh_542 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wf'45'fresh_542 = erased
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-heap
d_wf'45'heap_544 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_wf'45'heap_544 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_746 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-regs
d_wf'45'regs_546 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_wf'45'regs_546 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_742 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.StoreWF.wf-stack
d_wf'45'stack_548 ::
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  AgdaAny -> Integer -> AgdaAny
d_wf'45'stack_548 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_752
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.PtrB
d_PtrB_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_PtrB_550 = erased
-- Once.CCC.Machine.FlatPtrBounds.PtrB?
d_PtrB'63'_558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_PtrB'63'_558 = erased
-- Once.CCC.Machine.FlatPtrBounds.PBInv
d_PBInv_570 a0 a1 a2 = ()
data T_PBInv_570
  = C_mkPtrBounds_604 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
                       AgdaAny)
                      (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny)
                      (AgdaAny -> Integer -> AgdaAny)
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-regs
d_pb'45'regs_592 ::
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 -> AgdaAny
d_pb'45'regs_592 v0
  = case coe v0 of
      C_mkPtrBounds_604 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-heap
d_pb'45'heap_596 ::
  T_PBInv_570 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> AgdaAny
d_pb'45'heap_596 v0
  = case coe v0 of
      C_mkPtrBounds_604 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PBInv.pb-stack
d_pb'45'stack_602 :: T_PBInv_570 -> AgdaAny -> Integer -> AgdaAny
d_pb'45'stack_602 v0
  = case coe v0 of
      C_mkPtrBounds_604 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.PtrBoundsWF
d_PtrBoundsWF_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_PtrBoundsWF_606 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-suc
d_ptr'45'bounds'45'suc_616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_570 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'suc_616 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_ptr'45'bounds'45'suc_616 v2 v4
du_ptr'45'bounds'45'suc_616 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  T_PBInv_570 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'suc_616 v0 v1 = coe d_pb'45'regs_592 v1 v0
-- Once.CCC.Machine.FlatPtrBounds.ptr-bounds-cell
d_ptr'45'bounds'45'cell_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_570 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ptr'45'bounds'45'cell_634 ~v0 ~v1 v2 v3 v4 ~v5
  = du_ptr'45'bounds'45'cell_634 v2 v3 v4
du_ptr'45'bounds'45'cell_634 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_PBInv_570 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ptr'45'bounds'45'cell_634 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
               (coe v1))))
      (coe du_ptr'45'bounds'45'suc_616 (coe v0) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.size-with-new
d_size'45'with'45'new_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'new_652 = erased
-- Once.CCC.Machine.FlatPtrBounds.size-with-old
d_size'45'with'45'old_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'with'45'old_686 = erased
-- Once.CCC.Machine.FlatPtrBounds.ptrb-ext
d_ptrb'45'ext_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ptrb'45'ext_732 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_ptrb'45'ext_732 v4 v6
du_ptrb'45'ext_732 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_ptrb'45'ext_732 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v2
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pbm-ext
d_pbm'45'ext_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pbm'45'ext_780 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_pbm'45'ext_780 v4 v6
du_pbm'45'ext_780 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny
du_pbm'45'ext_780 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_ptrb'45'ext_732 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-halt
d_pb'45'halt_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool -> T_PBInv_570 -> T_PBInv_570
d_pb'45'halt_806 ~v0 ~v1 ~v2 ~v3 v4 = du_pb'45'halt_806 v4
du_pb'45'halt_806 :: T_PBInv_570 -> T_PBInv_570
du_pb'45'halt_806 v0 = coe v0
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg
d_pb'45'write'45'reg_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'write'45'reg_824 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'reg_824 v3 v5 v6
du_pb'45'write'45'reg_824 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'write'45'reg_824 v0 v1 v2
  = coe
      C_mkPtrBounds_604
      (coe
         (\ v3 ->
            coe
              du_go_844 (coe v1) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_642
                 (coe v0) (coe v3))))
      (coe d_pb'45'heap_596 (coe v2)) (coe d_pb'45'stack_602 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_844 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 = du_go_844 v5 v6 v7 v8
du_go_844 ::
  AgdaAny ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_844 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe d_pb'45'regs_592 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-reg-halt
d_pb'45'write'45'reg'45'halt_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Bool ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'write'45'reg'45'halt_876 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du_pb'45'write'45'reg'45'halt_876 v3 v7 v8
du_pb'45'write'45'reg'45'halt_876 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'write'45'reg'45'halt_876 v0 v1 v2
  = coe du_pb'45'write'45'reg_824 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.FlatPtrBounds.pb-wsm-aux
d_pb'45'wsm'45'aux_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'wsm'45'aux_914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                       v11
  = du_pb'45'wsm'45'aux_914 v6 v7 v10 v11
du_pb'45'wsm'45'aux_914 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'wsm'45'aux_914 v0 v1 v2 v3
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
-- Once.CCC.Machine.FlatPtrBounds.pb-whm-aux
d_pb'45'whm'45'aux_952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_pb'45'whm'45'aux_952 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_pb'45'whm'45'aux_952 v4 v7 v8
du_pb'45'whm'45'aux_952 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_pb'45'whm'45'aux_952 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v2)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-write-stack
d_pb'45'write'45'stack_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'write'45'stack_980 v0 ~v1 ~v2 v3 v4 ~v5 v6 v7
  = du_pb'45'write'45'stack_980 v0 v3 v4 v6 v7
du_pb'45'write'45'stack_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'write'45'stack_980 v0 v1 v2 v3 v4
  = coe
      C_mkPtrBounds_604 (coe d_pb'45'regs_592 (coe v4))
      (coe d_pb'45'heap_596 (coe v4))
      (coe
         (\ v5 v6 ->
            coe
              du_pb'45'wsm'45'aux_914
              (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 v0 v1 v5)
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2) (coe v6))
              (coe d_pb'45'stack_602 v4 v5 v6) (coe v3)))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-heap
d_pb'45'write'45'heap_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'write'45'heap_1008 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'heap_1008 v3 v5 v6
du_pb'45'write'45'heap_1008 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'write'45'heap_1008 v0 v1 v2
  = coe
      C_mkPtrBounds_604 (coe d_pb'45'regs_592 (coe v2))
      (coe
         (\ v3 ->
            coe
              du_pb'45'whm'45'aux_952
              (coe
                 MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v0)
                 (coe v3))
              (coe d_pb'45'heap_596 v2 v3) (coe v1)))
      (coe d_pb'45'stack_602 (coe v2))
-- Once.CCC.Machine.FlatPtrBounds.pb-write-mem
d_pb'45'write'45'mem_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'write'45'mem_1032 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'write'45'mem_1032 v0 v3 v5 v6
du_pb'45'write'45'mem_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'write'45'mem_1032 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_pb'45'write'45'stack_980 (coe v0) (coe v4) (coe v5) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe du_pb'45'write'45'heap_1008 (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-read-loc
d_pb'45'read'45'loc_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_pb'45'read'45'loc_1066 ~v0 ~v1 ~v2 v3 v4
  = du_pb'45'read'45'loc_1066 v3 v4
du_pb'45'read'45'loc_1066 ::
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
du_pb'45'read'45'loc_1066 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_pb'45'stack_602 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_pb'45'heap_596 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-value
d_pb'45'load'45'value_1094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'load'45'value_1094 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_pb'45'load'45'value_1094 v3 v4 v5 v6
du_pb'45'load'45'value_1094 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'load'45'value_1094 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe du_pb'45'write'45'reg_824 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-resolved
d_pb'45'load'45'resolved_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'load'45'resolved_1126 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'resolved_1126 v2 v3 v4 v5
du_pb'45'load'45'resolved_1126 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_570 -> T_PBInv_570
du_pb'45'load'45'resolved_1126 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_1094 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v0)
                (coe v4))
             (coe du_pb'45'read'45'loc_1066 (coe v3) (coe v4)) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-load-suc-resolved
d_pb'45'load'45'suc'45'resolved_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'load'45'suc'45'resolved_1154 ~v0 ~v1 v2 v3 v4 v5
  = du_pb'45'load'45'suc'45'resolved_1154 v2 v3 v4 v5
du_pb'45'load'45'suc'45'resolved_1154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_PBInv_570 -> T_PBInv_570
du_pb'45'load'45'suc'45'resolved_1154 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'load'45'value_1094 (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v0)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe
                du_pb'45'read'45'loc_1066 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4)))
             (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-resolved
d_pb'45'store'45'resolved_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'store'45'resolved_1182 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'resolved_1182 v0 v3 v5 v6
du_pb'45'store'45'resolved_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'store'45'resolved_1182 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_1032 (coe v0) (coe v4) (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-store-suc-resolved
d_pb'45'store'45'suc'45'resolved_1214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'store'45'suc'45'resolved_1214 v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_pb'45'store'45'suc'45'resolved_1214 v0 v3 v5 v6
du_pb'45'store'45'suc'45'resolved_1214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'store'45'suc'45'resolved_1214 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_pb'45'write'45'mem_1032 (coe v0)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
             (coe v2) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-from-slot
d_pb'45'from'45'slot_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'from'45'slot_1244 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'from'45'slot_1244 v3 v4 v5
du_pb'45'from'45'slot_1244 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'from'45'slot_1244 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-restore
d_pb'45'restore_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
d_pb'45'restore_1270 ~v0 ~v1 ~v2 v3 v4 v5
  = du_pb'45'restore_1270 v3 v4 v5
du_pb'45'restore_1270 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> T_PBInv_570 -> T_PBInv_570
du_pb'45'restore_1270 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) (coe v1)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-pred
d_pb'45'pred_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_pb'45'pred_1294 ~v0 ~v1 v2 = du_pb'45'pred_1294 v2
du_pb'45'pred_1294 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_pb'45'pred_1294 v0
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
-- Once.CCC.Machine.FlatPtrBounds.pb-succ
d_pb'45'succ_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
d_pb'45'succ_1320 ~v0 ~v1 v2 = du_pb'45'succ_1320 v2
du_pb'45'succ_1320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> AgdaAny
du_pb'45'succ_1320 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-reg-op
d_pb'45'reg'45'op_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'reg'45'op_1346 ~v0 ~v1 v2 v3 v4
  = du_pb'45'reg'45'op_1346 v2 v3 v4
du_pb'45'reg'45'op_1346 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_368 ->
  T_PBInv_570 -> T_PBInv_570
du_pb'45'reg'45'op_1346 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe
                du_pb'45'pred_1294
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)
             (coe
                d_pb'45'regs_592 v2
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62))
             (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)
             (coe
                du_pb'45'succ_1320
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_62)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds
d_structured'45'pure'45'sigop'45'inbounds_1394
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.FlatPtrBounds.structured-pure-sigop-inbounds"
-- Once.CCC.Machine.FlatPtrBounds.res-sv-pb
d_res'45'sv'45'pb_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
d_res'45'sv'45'pb_1404 ~v0 ~v1 ~v2 ~v3 v4
  = du_res'45'sv'45'pb_1404 v4
du_res'45'sv'45'pb_1404 :: MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_res'45'sv'45'pb_1404 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.sigop-output-pb
d_sigop'45'output'45'pb_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> AgdaAny
d_sigop'45'output'45'pb_1426 v0 v1 v2 v3 v4 v5
  = coe
      d_go_1468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v4))
-- Once.CCC.Machine.FlatPtrBounds._.pov
d_pov_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> Maybe AgdaAny -> AgdaAny
d_pov_1446 v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 = du_pov_1446 v0 v2 v3 v4 v7
du_pov_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny -> AgdaAny
du_pov_1446 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_res'45'sv'45'pb_1404
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_342 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_162 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166
                   (coe v0))
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.aux
d_aux_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny
d_aux_1458 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_pov_1446 (coe v0) (coe v2) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2810 (coe v2)
                       (coe v9) (coe v5))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pov_1446 (coe v0) (coe v2) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2754
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v5))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_structured'45'pure'45'sigop'45'inbounds_1394 v0 v1 v2 v3 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 -> AgdaAny
d_go_1468 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe
             d_aux_1458 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v3))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v5))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe
             du_cv_1476 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._._.cv
d_cv_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny
d_cv_1476 v0 ~v1 v2 v3 v4 v5 v6 = du_cv_1476 v0 v2 v3 v4 v5 v6
du_cv_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny
du_cv_1476 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_ans_1486 (coe v1) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'dec_2954
                (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._._._.ans
d_ans_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_ans_1486 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 = du_ans_1486 v2 v4 v5 v7
du_ans_1486 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_ans_1486 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_at_1496
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2860 (coe v0)
                          (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                          (coe v2)))
             else coe seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._._._._.at
d_at_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> AgdaAny
d_at_1496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_at_1496 v8
du_at_1496 :: Maybe AgdaAny -> AgdaAny
du_at_1496 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.CCC.Machine.FlatPtrBounds.pb-abstract
d_pb'45'abstract_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'abstract_1506 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2238
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe
                     d_pb'45'regs_592 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2240
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
                  (coe
                     d_pb'45'regs_592 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2242
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'resolved_1126 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2244
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'load'45'suc'45'resolved_1154 (coe v2)
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2246 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1244
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_1066 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2248 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_1032 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_592 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2250
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'resolved_1182 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_592 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2252
        -> coe
             (\ v2 v3 v4 v5 v6 v7 ->
                coe
                  du_pb'45'store'45'suc'45'resolved_1214 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v2))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                  (coe
                     d_pb'45'regs_592 v7
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                  (coe v7))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2254 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2256 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'restore_1270
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_1066 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2258 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2260 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2262 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2264 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2266
        -> coe (\ v2 v3 v4 v5 v6 v7 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2268
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2270 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2272 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'mem_1032 (coe v0)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                        (coe v4))
                     (coe v2))
                  (coe
                     d_pb'45'regs_592 v8
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2274 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'from'45'slot_1244
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654 (coe v3)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe
                     du_pb'45'read'45'loc_1066 (coe v8)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                           (coe v4))
                        (coe v2)))
                  (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2276 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2282 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg'45'halt_876
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe
                     d_sigop'45'output'45'pb_1426 (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3220
                              (coe v0) (coe v1) (coe v5) (coe v6))))
                     (coe v2) (coe v3) (coe v4) (coe v5))
                  (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2288 v2 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v10))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2290 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2292
        -> coe (\ v2 v3 v4 v5 v6 v7 -> v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2294 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  du_pb'45'write'45'reg_824
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2296 v2 v3
        -> coe (\ v4 v5 v6 v7 v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2298 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe
                  C_mkPtrBounds_604
                  (coe
                     (\ v9 ->
                        coe
                          du_go_1902 (coe v2) (coe v3) (coe v6) (coe v8) (coe v9)
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.du_readReg'45'write_642
                             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) (coe v9))))
                  (coe
                     (\ v9 ->
                        coe
                          du_pbm'45'ext_780
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 v3 v9)
                          (coe d_pb'45'heap_596 v8 v9)))
                  (coe
                     (\ v9 v10 ->
                        coe
                          du_pbm'45'ext_780
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 v3 v9 v10)
                          (coe d_pb'45'stack_602 v8 v9 v10))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2300 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2302 v2
        -> coe
             (\ v3 v4 v5 v6 v7 v8 ->
                coe du_pb'45'reg'45'op_1346 (coe v3) (coe v2) (coe v8))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> v8)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2306 v2
        -> coe (\ v3 v4 v5 v6 v7 v8 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds._.st
d_st_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 -> Integer
d_st_1890 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_st_1890 v3
du_st_1890 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 -> Integer
du_st_1890 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_592
      (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.bs
d_bs_1892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 -> Integer -> Integer
d_bs_1892 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_bs_1892 v3
du_bs_1892 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Integer
du_bs_1892 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594 (coe v0)
-- Once.CCC.Machine.FlatPtrBounds._.fresh
d_fresh_1894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fresh_1894 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_fresh_1894 v3
du_fresh_1894 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_fresh_1894 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe du_st_1890 (coe v0)))
            (coe (0 :: Integer))))
-- Once.CCC.Machine.FlatPtrBounds._.fresh-ok
d_fresh'45'ok_1896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fresh'45'ok_1896 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_fresh'45'ok_1896 v1 v5
du_fresh'45'ok_1896 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fresh'45'ok_1896 v0 v1 = coe v1 v0 erased
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_1902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_go_1902 ~v0 v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_go_1902 v1 v2 v5 v7 v8 v9
du_go_1902 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_go_1902 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_fresh'45'ok_1896 (coe v0) (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_ptrb'45'ext_732
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))
                (coe v4))
             (coe d_pb'45'regs_592 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.FlatPtrBounds.pb-jump
d_pb'45'jump_1960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'jump_1960 ~v0 v1 ~v2 v3 = du_pb'45'jump_1960 v1 v3
du_pb'45'jump_1960 :: Maybe Integer -> T_PBInv_570 -> T_PBInv_570
du_pb'45'jump_1960 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-ret
d_pb'45'ret_1976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'ret_1976 ~v0 v1 ~v2 v3 = du_pb'45'ret_1976 v1 v3
du_pb'45'ret_1976 :: [Integer] -> T_PBInv_570 -> T_PBInv_570
du_pb'45'ret_1976 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.pb-thunk
d_pb'45'thunk_1998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'thunk_1998 v0 v1 v2 v3
  = coe
      C_mkPtrBounds_604 (coe d_pb'45'regs_592 (coe v3))
      (coe d_pb'45'heap_596 (coe v3))
      (coe d_cleared_2014 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.FlatPtrBounds._.cleared
d_cleared_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> AgdaAny -> Integer -> AgdaAny
d_cleared_2014 v0 v1 v2 v3 v4 v5
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
                                    else coe seq (coe v11) (coe d_pb'45'stack_602 v3 v4 v5)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe seq (coe v9) (coe d_pb'45'stack_602 v3 v4 v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.FlatPtrBounds.pb-branch
d_pb'45'branch_2044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'branch_2044 v0 v1 v2 v3 ~v4 v5
  = du_pb'45'branch_2044 v0 v1 v2 v3 v5
du_pb'45'branch_2044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  T_PBInv_570 -> T_PBInv_570
du_pb'45'branch_2044 v0 v1 v2 v3 v4
  = if coe v1
      then coe
             du_pb'45'jump_1960
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                (coe v3) (coe v2))
             (coe v4)
      else coe v4
-- Once.CCC.Machine.FlatPtrBounds.pb-call
d_pb'45'call_2066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'call_2066 v0 v1 v2 v3
  = coe
      du_go_2078 (coe v3)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_callView_1368 (coe v0)
         (coe v1) (coe v2))
-- Once.CCC.Machine.FlatPtrBounds._.go
d_go_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_PBInv_570
d_go_2078 ~v0 ~v1 ~v2 v3 v4 = du_go_2078 v3 v4
du_go_2078 ::
  T_PBInv_570 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_CallPost_1350 -> T_PBInv_570
du_go_2078 v0 v1 = coe seq (coe v1) (coe v0)
-- Once.CCC.Machine.FlatPtrBounds.pb-call-at
d_pb'45'call'45'at_2102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_PBInv_570 -> T_PBInv_570
d_pb'45'call'45'at_2102 ~v0 v1 ~v2 v3
  = du_pb'45'call'45'at_2102 v1 v3
du_pb'45'call'45'at_2102 ::
  Maybe Integer -> T_PBInv_570 -> T_PBInv_570
du_pb'45'call'45'at_2102 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.FlatPtrBounds.flat-ptr-bounds
d_flat'45'ptr'45'bounds_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2236] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_716 ->
  T_PBInv_570 -> T_PBInv_570
d_flat'45'ptr'45'bounds_2122 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2238
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2240
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2242
        -> coe
             du_pb'45'load'45'resolved_1126
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2244
        -> coe
             du_pb'45'load'45'suc'45'resolved_1154
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2246 v8
        -> coe
             du_pb'45'from'45'slot_1244
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_1066 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2248 v8
        -> coe
             du_pb'45'write'45'mem_1032 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2250
        -> coe
             du_pb'45'store'45'resolved_1182 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2252
        -> coe
             du_pb'45'store'45'suc'45'resolved_1214 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2254 v8
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2256 v8
        -> coe
             du_pb'45'restore_1270
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_1066 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2262 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2268
        -> coe d_pb'45'call_2066 (coe v0) (coe v2) (coe v3) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2270 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2272 v8
        -> coe
             du_pb'45'write'45'mem_1032 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                (coe v8))
             (coe
                d_pb'45'regs_592 v7
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2274 v8
        -> coe
             du_pb'45'from'45'slot_1244
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe
                du_pb'45'read'45'loc_1066 (coe v7)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
                   (coe v8)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2276 v8
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2282 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg'45'halt_876
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe
                d_sigop'45'output'45'pb_1426 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_594
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3220
                         (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
                         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))))
                (coe v8) (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
             (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2288 v8 v9 v10
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2290 v8
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2292
        -> coe v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2294 v8
        -> coe
             du_pb'45'write'45'reg_824
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2298 v8
        -> coe
             d_pb'45'abstract_1506 v0 v1
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)) v4 v5 v6
             v7
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2302 v8
        -> coe
             du_pb'45'reg'45'op_1346
             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))
             (coe v8) (coe v7)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2304 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2216 v9 -> coe v7
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2218 v9
               -> coe
                    du_pb'45'jump_1960
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2220 v9
               -> coe
                    du_pb'45'branch_2044 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416
                             (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3)))
                          (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2222 v9
               -> coe
                    du_pb'45'branch_2044 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.du_tag'45'zf_106
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.Flat.du_flat'45'read'45'tag_118
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v3))))
                    (coe v9) (coe v2) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2224 v9 v10
               -> coe d_pb'45'thunk_1998 (coe v0) (coe v10) (coe v3) (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2226 v9
               -> coe
                    du_pb'45'ret_1976
                    (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v3))
                    (coe v7)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2228 v9
               -> coe
                    du_pb'45'call'45'at_2102
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'fn_240 (coe v0)
                       (coe v2) (coe v9))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
