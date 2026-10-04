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

module MAlonzo.Code.Once.CCC.Machine.SMPrimitives where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
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
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CCC.Machine.SMPrimitives.Frame
d_Frame_10 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_Frame_10 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.clear-frame
d_clear'45'frame_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_710 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.clear-frame-aux
d_clear'45'frame'45'aux_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_clear'45'frame'45'aux_22 ~v0 = du_clear'45'frame'45'aux_22
du_clear'45'frame'45'aux_22 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_clear'45'frame'45'aux_22 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_clear'45'frame'45'aux_704
      v4 v5 v6
-- Once.CCC.Machine.SMPrimitives.Ops._.clear-frame-just
d_clear'45'frame'45'just_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_24 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.readHeapLoc
d_readHeapLoc_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readHeapLoc_26 v0 v1
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 v0 v1
-- Once.CCC.Machine.SMPrimitives.Ops._.readLoc
d_readLoc_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_28 ~v0 = du_readLoc_28
du_readLoc_28 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_28
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.Ops._.readStackLoc
d_readStackLoc_30 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readStackLoc_30 v0 v1 v2
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 v0 v1 v2
-- Once.CCC.Machine.SMPrimitives.Ops._.writeHeapMem
d_writeHeapMem_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem_32 ~v0 = du_writeHeapMem_32
du_writeHeapMem_32 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem_32
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_792
-- Once.CCC.Machine.SMPrimitives.Ops._.writeHeapMem-aux
d_writeHeapMem'45'aux_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem'45'aux_34 ~v0 = du_writeHeapMem'45'aux_34
du_writeHeapMem'45'aux_34 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem'45'aux_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem'45'aux_786 v2
      v3 v4
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc
d_writeLoc_36 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_36 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-halted
d_writeLoc'45'halted_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_38 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_40 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_40 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_42 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_44 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_46 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-regs
d_writeLoc'45'regs_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_48 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_50 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLocToHeap
d_writeLocToHeap_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_52 ~v0 = du_writeLocToHeap_52
du_writeLocToHeap_52 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_52
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_812
-- Once.CCC.Machine.SMPrimitives.Ops._.writeLocToStack
d_writeLocToStack_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_54 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_802 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.writeStackMem
d_writeStackMem_56 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeStackMem_56 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_682 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.writeStackMem-aux
d_writeStackMem'45'aux_58 ::
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
d_writeStackMem'45'aux_58 ~v0 = du_writeStackMem'45'aux_58
du_writeStackMem'45'aux_58 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeStackMem'45'aux_58 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeStackMem'45'aux_674 v4
      v5 v6 v7
-- Once.CCC.Machine.SMPrimitives.Ops._.AllI
d_AllI_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_AllI_62 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.BodyRunner
d_BodyRunner_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_64 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.call-sigop-ans
d_call'45'sigop'45'ans_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans_2940
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'ans'45'at_68 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'ans'45'at_2910
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.call-sigop-dec
d_call'45'sigop'45'dec_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'dec_2962
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.call-sigop-output
d_call'45'sigop'45'output_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'output_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'output_2990
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.call-sigop-val
d_call'45'sigop'45'val_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_call'45'sigop'45'val_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_call'45'sigop'45'val_2974
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.case-tag-at
d_case'45'tag'45'at_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_case'45'tag'45'at_76 ~v0 = du_case'45'tag'45'at_76
du_case'45'tag'45'at_76 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_case'45'tag'45'at_76
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_case'45'tag'45'at_3134
-- Once.CCC.Machine.SMPrimitives.Ops._.combine-typed
d_combine'45'typed_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_78 ~v0 = du_combine'45'typed_78
du_combine'45'typed_78 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_combine'45'typed_2694 v2 v3
-- Once.CCC.Machine.SMPrimitives.Ops._.decode-at
d_decode'45'at_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_decode'45'at_80 ~v0 = du_decode'45'at_80
du_decode'45'at_80 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_decode'45'at_80
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_decode'45'at_2868
-- Once.CCC.Machine.SMPrimitives.Ops._.events-at-arg
d_events'45'at'45'arg_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_events'45'at'45'arg_82 ~v0 = du_events'45'at'45'arg_82
du_events'45'at'45'arg_82 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_events'45'at'45'arg_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_events'45'at'45'arg_2884 v0
      v2 v3
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-abstract
d_exec'45'abstract_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_86 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-case-dispatch
d_exec'45'case'45'dispatch_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_88 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_3234
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_90 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_90 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_92 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_94 ~v0
  = du_exec'45'load'45'from'45'slot'45'with'45'value_94
du_exec'45'load'45'from'45'slot'45'with'45'value_94 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_94
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'from'45'slot'45'with'45'value_2636
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-loop
d_exec'45'loop_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'loop_3232 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-loop-run
d_exec'45'loop'45'run_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_98 ~v0 = du_exec'45'loop'45'run_98
du_exec'45'loop'45'run_98 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_98
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'loop'45'run_3162
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-restore-input-just
d_exec'45'restore'45'input'45'just_100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_100 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_102 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_104 ~v0
  = du_exec'45'restore'45'input'45'with'45'value_104
du_exec'45'restore'45'input'45'with'45'value_104 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'restore'45'input'45'with'45'value_2648
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-sigop-halts
d_exec'45'sigop'45'halts_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_106 ~v0 = du_exec'45'sigop'45'halts_106
du_exec'45'sigop'45'halts_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_3126
      v2
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_108 ~v0
  = du_exec'45'sigop'45'halts'45'of_108
du_exec'45'sigop'45'halts'45'of_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 -> Bool
du_exec'45'sigop'45'halts'45'of_108 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts'45'of_3120
      v2
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-sigop-output
d_exec'45'sigop'45'output_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output_110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output_3110
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_3068
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-trace
d_exec'45'trace_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_114 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-trace-++
d_exec'45'trace'45''43''43'_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_116 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_118 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-trace-cons
d_exec'45'trace'45'cons_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_120 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-trace-single
d_exec'45'trace'45'single_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_122 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_124 ~v0
  = du_exec'45'tree'45'flat'45'equiv'45'simple_124
du_exec'45'tree'45'flat'45'equiv'45'simple_124 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_124 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'tree'45'flat'45'equiv'45'simple_4260
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace
d_exec'45'tree'45'trace_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_126 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'tree'45'trace_3870
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_128 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_130 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_132 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_TreeTrace_2426 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_134 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_136 = erased
-- Once.CCC.Machine.SMPrimitives.Ops._.getTag
d_getTag_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Maybe Integer
d_getTag_138 ~v0 = du_getTag_138
du_getTag_138 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> Maybe Integer
du_getTag_138
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_getTag_3846
-- Once.CCC.Machine.SMPrimitives.Ops._.lit-value
d_lit'45'value_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny -> AgdaAny
d_lit'45'value_140 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_lit'45'value_3222 (coe v0)
      v2 v3
-- Once.CCC.Machine.SMPrimitives.Ops._.loop-fuel
d_loop'45'fuel_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_loop'45'fuel_142 ~v0 = du_loop'45'fuel_142
du_loop'45'fuel_142 :: Integer
du_loop'45'fuel_142
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'fuel_3132
-- Once.CCC.Machine.SMPrimitives.Ops._.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_loop'45'reanchor'45'alloc_144 ~v0
  = du_loop'45'reanchor'45'alloc_144
du_loop'45'reanchor'45'alloc_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_loop'45'reanchor'45'alloc_144
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'alloc_3156
-- Once.CCC.Machine.SMPrimitives.Ops._.loop-reanchor-loc
d_loop'45'reanchor'45'loc_146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_loop'45'reanchor'45'loc_146 ~v0 = du_loop'45'reanchor'45'loc_146
du_loop'45'reanchor'45'loc_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_loop'45'reanchor'45'loc_146
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_loop'45'reanchor'45'loc_3150
-- Once.CCC.Machine.SMPrimitives.Ops._.machine-events
d_machine'45'events_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_148 ~v0 = du_machine'45'events_148
du_machine'45'events_148 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_machine'45'events_2898 v0
      v2 v3
-- Once.CCC.Machine.SMPrimitives.Ops._.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_150 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'aux_3032
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'out'45'val_152 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'out'45'val_3008
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.pure-sigop-output
d_pure'45'sigop'45'output_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_pure'45'sigop'45'output_154 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_pure'45'sigop'45'output_3002
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.Ops._.readReg-typed
d_readReg'45'typed_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_156 ~v0 = du_readReg'45'typed_156
du_readReg'45'typed_156 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_156
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2762
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped
d_readTyped_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_158 ~v0 = du_readTyped_158
du_readTyped_158 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_158
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2818
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped-cell
d_readTyped'45'cell_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_160 ~v0 = du_readTyped'45'cell_160
du_readTyped'45'cell_160 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_160 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2710 v1
      v2 v3
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped-float
d_readTyped'45'float_162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_readTyped'45'float_162 ~v0 = du_readTyped'45'float_162
du_readTyped'45'float_162 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_readTyped'45'float_162
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'float_2704
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped-int
d_readTyped'45'int_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_readTyped'45'int_164 ~v0 = du_readTyped'45'int_164
du_readTyped'45'int_164 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_readTyped'45'int_164
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'int_2700
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped-pair
d_readTyped'45'pair_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_166 ~v0 = du_readTyped'45'pair_166
du_readTyped'45'pair_166 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_166 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'pair_2746 v2
      v3 v4 v5 v6 v7
-- Once.CCC.Machine.SMPrimitives.Ops._.readTyped-sum
d_readTyped'45'sum_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_168 ~v0 = du_readTyped'45'sum_168
du_readTyped'45'sum_168 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  (Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_168 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'sum_2772 v2 v3
      v4 v5
-- Once.CCC.Machine.SMPrimitives.Ops._.res-sv
d_res'45'sv_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_res'45'sv_170 ~v0 = du_res'45'sv_170
du_res'45'sv_170 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_res'45'sv_170
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_res'45'sv_3012
-- Once.CCC.Machine.SMPrimitives.Ops._.sigop-events
d_sigop'45'events_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_172 ~v0 = du_sigop'45'events_172
du_sigop'45'events_172 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_172 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events_3100 v0 v2
      v3
-- Once.CCC.Machine.SMPrimitives.Ops._.sigop-events-of
d_sigop'45'events'45'of_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_174 ~v0 = du_sigop'45'events'45'of_174
du_sigop'45'events'45'of_174 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_174 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_sigop'45'events'45'of_3082
      v0 v2 v3 v4
-- Once.CCC.Machine.SMPrimitives.Ops._.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_structured'45'pure'45'sigop'45'output_176 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_structured'45'pure'45'sigop'45'output_2864
      v0
-- Once.CCC.Machine.SMPrimitives.Ops._.unit-storedvalue
d_unit'45'storedvalue_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_unit'45'storedvalue_178 ~v0 = du_unit'45'storedvalue_178
du_unit'45'storedvalue_178 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_unit'45'storedvalue_178
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_unit'45'storedvalue_2688
-- Once.CCC.Machine.SMPrimitives.stack-slot-disjoint
d_stack'45'slot'45'disjoint_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'slot'45'disjoint_188 = erased
-- Once.CCC.Machine.SMPrimitives.stack-frame-injective
d_stack'45'frame'45'injective_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'frame'45'injective_208 = erased
-- Once.CCC.Machine.SMPrimitives.stack-slot-injective
d_stack'45'slot'45'injective_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'slot'45'injective_220 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps._.readLoc
d_readLoc_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_236 ~v0 = du_readLoc_236
du_readLoc_236 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_236
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.MemoryOps._.writeLoc
d_writeLoc_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_244 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-stack-heap
d_readLoc'45'writeLoc'45'stack'45'heap_286 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'heap_286 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-heap-stack
d_readLoc'45'writeLoc'45'heap'45'stack_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'heap'45'stack_308 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-heapMem-eq
d_readLoc'45'heapMem'45'eq_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'heapMem'45'eq_356 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.writeLoc-regs-commute-heap
d_writeLoc'45'regs'45'commute'45'heap_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'heap_398 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.writeLoc-regs-commute-general
d_writeLoc'45'regs'45'commute'45'general_440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'general_440 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-stack-slot-lt
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_470 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-stack-slot-gt
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_538 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-stack-ancestor
d_readLoc'45'writeLoc'45'stack'45'ancestor_608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'ancestor_608 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps.readLoc-writeLoc-same
d_readLoc'45'writeLoc'45'same_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'same_666 = erased
-- Once.CCC.Machine.SMPrimitives.MemoryOps._.readLoc-writeLoc-same-heap
d_readLoc'45'writeLoc'45'same'45'heap_692
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.MemoryOps._.readLoc-writeLoc-same-heap"
-- Once.CCC.Machine.SMPrimitives.instr-writes-slot
d_instr'45'writes'45'slot_694 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe Integer
d_instr'45'writes'45'slot_694 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.instr-reads-slot
d_instr'45'reads'45'slot_700 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe Integer
d_instr'45'reads'45'slot_700 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.instr-writes-heap-indirect-aux
d_instr'45'writes'45'heap'45'indirect'45'aux_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_instr'45'writes'45'heap'45'indirect'45'aux_710 ~v0 v1
  = du_instr'45'writes'45'heap'45'indirect'45'aux_710 v1
du_instr'45'writes'45'heap'45'indirect'45'aux_710 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_instr'45'writes'45'heap'45'indirect'45'aux_710 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.instr-writes-heap-indirect-suc-aux
d_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714 ~v0 v1
  = du_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714 v1
du_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.instr-writes-heap
d_instr'45'writes'45'heap_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_instr'45'writes'45'heap_718 ~v0 v1 v2
  = du_instr'45'writes'45'heap_718 v1 v2
du_instr'45'writes'45'heap_718 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_instr'45'writes'45'heap_718 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe
             du_instr'45'writes'45'heap'45'indirect'45'aux_710
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe
             du_instr'45'writes'45'heap'45'indirect'45'suc'45'aux_714
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.InSomeRegion
d_InSomeRegion_724 a0 a1 = ()
data T_InSomeRegion_724
  = C_in'45'head_732 MAlonzo.Code.Once.CCC.Machine.SMCore.T_InRegion_28 |
    C_in'45'tail_740 T_InSomeRegion_724
-- Once.CCC.Machine.SMPrimitives.InstrWritesWithinOwned
d_InstrWritesWithinOwned_750 a0 a1 a2 a3 = ()
data T_InstrWritesWithinOwned_750
  = C_no'45'heap'45'write_758 |
    C_heap'45'write'45'owned_762 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
                                 T_InSomeRegion_724
-- Once.CCC.Machine.SMPrimitives.InstrNoHeapWrite
d_InstrNoHeapWrite_764 a0 = ()
data T_InstrNoHeapWrite_764
  = C_nhw'45'mov'45'to'45'output_766 |
    C_nhw'45'instr'45'reg'45'op_770 | C_nhw'45'instr'45'ctrl_774 |
    C_nhw'45'mov'45'to'45'input_776 | C_nhw'45'load'45'indirect_778 |
    C_nhw'45'load'45'indirect'45'suc_780 |
    C_nhw'45'load'45'from'45'slot_784 |
    C_nhw'45'store'45'at'45'slot_788 | C_nhw'45'lea'45'slot_792 |
    C_nhw'45'restore'45'input_796 | C_nhw'45'lea'45'indexed_800 |
    C_nhw'45'instr'45'alloc'45'stack_804 |
    C_nhw'45'instr'45'dealloc'45'stack_808 |
    C_nhw'45'instr'45'reclaim'45'to_812 |
    C_nhw'45'instr'45'push'45'frame_816 |
    C_nhw'45'instr'45'pop'45'frame_818 |
    C_nhw'45'instr'45'call'45'closure_820 |
    C_nhw'45'worklist'45'init_824 | C_nhw'45'worklist'45'push_828 |
    C_nhw'45'worklist'45'pop_832 | C_nhw'45'worklist'45'check_836 |
    C_nhw'45'instr'45'sigop_844 | C_nhw'45'instr'45'load'45'const_852 |
    C_nhw'45'instr'45'load'45'tag'45'lit_856 |
    C_nhw'45'instr'45'load'45'code'45'addr_860 |
    C_nhw'45'instr'45'save'45'closure'45'reg_862 |
    C_nhw'45'instr'45'alloc'45'heap_866
-- Once.CCC.Machine.SMPrimitives.InstrPreservesFrame
d_InstrPreservesFrame_868 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrPreservesFrame_868 = erased
-- Once.CCC.Machine.SMPrimitives.InstrEffect
d_InstrEffect_878 = ()
data T_InstrEffect_878
  = C_eff'45'reg'45'only_880 | C_eff'45'stack'45'read_882 |
    C_eff'45'stack'45'write_884 | C_eff'45'stack'45'frontier_886 |
    C_eff'45'heap'45'alloc_888 | C_eff'45'heap'45'indirect_890 |
    C_eff'45'frame'45'op_892 | C_eff'45'control_894
-- Once.CCC.Machine.SMPrimitives.instr-effect
d_instr'45'effect_896 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_InstrEffect_878
d_instr'45'effect_896 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe C_eff'45'heap'45'indirect_890
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe C_eff'45'heap'45'indirect_890
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v1
        -> coe C_eff'45'stack'45'read_882
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v1
        -> coe C_eff'45'stack'45'write_884
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe C_eff'45'heap'45'indirect_890
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe C_eff'45'heap'45'indirect_890
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v1
        -> coe C_eff'45'stack'45'read_882
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v1
        -> coe C_eff'45'stack'45'frontier_886
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v1
        -> coe C_eff'45'stack'45'frontier_886
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v1
        -> coe C_eff'45'stack'45'frontier_886
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v1
        -> coe C_eff'45'frame'45'op_892
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe C_eff'45'frame'45'op_892
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe C_eff'45'control_894
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v1
        -> coe C_eff'45'stack'45'write_884
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v1
        -> coe C_eff'45'stack'45'write_884
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v1
        -> coe C_eff'45'stack'45'read_882
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v1 v2 v3
        -> coe C_eff'45'control_894
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v1 v2 v3
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v1 v2
        -> coe C_eff'45'heap'45'alloc_888
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v1
        -> coe C_eff'45'heap'45'alloc_888
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v1
        -> coe C_eff'45'heap'45'alloc_888
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v1
        -> coe C_eff'45'reg'45'only_880
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v1
        -> coe C_eff'45'stack'45'read_882
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.EffectPreservesNextHeapRef
d_EffectPreservesNextHeapRef_898 :: T_InstrEffect_878 -> ()
d_EffectPreservesNextHeapRef_898 = erased
-- Once.CCC.Machine.SMPrimitives.EffectStateOnlyDependsOnFrame
d_EffectStateOnlyDependsOnFrame_904 :: T_InstrEffect_878 -> ()
d_EffectStateOnlyDependsOnFrame_904 = erased
-- Once.CCC.Machine.SMPrimitives.instr-reads-mem
d_instr'45'reads'45'mem_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_instr'45'reads'45'mem_910 ~v0 v1 v2 v3
  = du_instr'45'reads'45'mem_910 v1 v2 v3
du_instr'45'reads'45'mem_910 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_instr'45'reads'45'mem_910 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> let v3
                 = coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_input1_136
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.instr-writes-mem
d_instr'45'writes'45'mem_1076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_instr'45'writes'45'mem_1076 ~v0 v1 v2 v3
  = du_instr'45'writes'45'mem_1076 v1 v2 v3
du_instr'45'writes'45'mem_1076 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_instr'45'writes'45'mem_1076 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2252
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2254
        -> let v3
                 = coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1370
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_input1_136
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v1))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_584
                   (coe v2))
                (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2298 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2302 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc
d_readLoc_1256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1256 ~v0 = du_readLoc_1256
du_readLoc_1256 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1256
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.exec-abstract
d_exec'45'abstract_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1366 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.exec-case-dispatch
d_exec'45'case'45'dispatch_1370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_1370 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'case'45'dispatch_3234
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.exec-loop
d_exec'45'loop_1378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_1378 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'loop_3232 (coe v0)
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.exec-trace
d_exec'45'trace_1396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_1396 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-heapMem-eq
d_readLoc'45'heapMem'45'eq_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'heapMem'45'eq_1464 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-heap-stack
d_readLoc'45'writeLoc'45'heap'45'stack_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'heap'45'stack_1466 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-same
d_readLoc'45'writeLoc'45'same_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'same_1468 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-stack-ancestor
d_readLoc'45'writeLoc'45'stack'45'ancestor_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'ancestor_1470 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-stack-heap
d_readLoc'45'writeLoc'45'stack'45'heap_1472 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'heap_1472 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-stack-slot-gt
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_1474 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.readLoc-writeLoc-stack-slot-lt
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_1476 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.writeLoc-regs-commute-general
d_writeLoc'45'regs'45'commute'45'general_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'general_1478 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives._.writeLoc-regs-commute-heap
d_writeLoc'45'regs'45'commute'45'heap_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'heap_1480 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.LocState-eq
d_LocState'45'eq_1492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LocState'45'eq_1492 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-deterministic
d_exec'45'abstract'45'deterministic_1524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'deterministic_1524 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-loop-preserves-frame
d_exec'45'loop'45'preserves'45'frame_1556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'loop'45'preserves'45'frame_1556 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_1642 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-trace-preserves-frame
d_exec'45'trace'45'preserves'45'frame_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'frame_1650 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-case-dispatch-preserves-frame
d_exec'45'case'45'dispatch'45'preserves'45'frame_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'case'45'dispatch'45'preserves'45'frame_1662 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_2080 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.worklist-push-preserves-stack-slot
d_worklist'45'push'45'preserves'45'stack'45'slot_2376
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.InstrPrimitives.worklist-push-preserves-stack-slot"
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_2388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_2388 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_2844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_2844 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.store-at-slot-preserves-above
d_store'45'at'45'slot'45'preserves'45'above_2864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'above_2864 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_2886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_2886 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.just-injective
d_just'45'injective_2906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injective_2906 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.REFUTABLE-effect-state-only-frame-dep
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2910
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.InstrPrimitives.REFUTABLE-effect-state-only-frame-dep"
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-same-frame
d_exec'45'abstract'45'same'45'frame_2920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'same'45'frame_2920 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.next-slot-update-preserves-frame
d_next'45'slot'45'update'45'preserves'45'frame_3500 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'frame_3500 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.next-slot-update-preserves-heap-ref
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_3506 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_3506 = erased
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.case-on-tag-state-next-slot-invariant
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_3518
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.InstrPrimitives.case-on-tag-state-next-slot-invariant"
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.loop-state-next-slot-invariant
d_loop'45'state'45'next'45'slot'45'invariant_3528
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.InstrPrimitives.loop-state-next-slot-invariant"
-- Once.CCC.Machine.SMPrimitives.InstrPrimitives.exec-abstract-state-next-slot-invariant
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_3538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_3538
  = erased
-- Once.CCC.Machine.SMPrimitives.TraceWritesAbove
d_TraceWritesAbove_3778 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceWritesAbove_3778 = erased
-- Once.CCC.Machine.SMPrimitives.TraceWritesBelow
d_TraceWritesBelow_3806 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceWritesBelow_3806 = erased
-- Once.CCC.Machine.SMPrimitives.twa-tail
d_twa'45'tail_3840 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_twa'45'tail_3840 ~v0 v1 ~v2 ~v3 v4 = du_twa'45'tail_3840 v1 v4
du_twa'45'tail_3840 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
du_twa'45'tail_3840 v0 v1
  = let v2 = d_instr'45'writes'45'slot_694 (coe v0) in
    coe (coe seq (coe v2) (coe v1))
-- Once.CCC.Machine.SMPrimitives.twb-tail
d_twb'45'tail_3882 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_twb'45'tail_3882 ~v0 v1 ~v2 ~v3 v4 = du_twb'45'tail_3882 v1 v4
du_twb'45'tail_3882 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
du_twb'45'tail_3882 v0 v1
  = let v2 = d_instr'45'writes'45'slot_694 (coe v0) in
    coe (coe seq (coe v2) (coe v1))
-- Once.CCC.Machine.SMPrimitives.TraceSlotReadsAbove
d_TraceSlotReadsAbove_3918 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceSlotReadsAbove_3918 = erased
-- Once.CCC.Machine.SMPrimitives.TraceSlotReadsBelow
d_TraceSlotReadsBelow_3946 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceSlotReadsBelow_3946 = erased
-- Once.CCC.Machine.SMPrimitives.TraceHeapOwnership.TraceWritesWithinOwned
d_TraceWritesWithinOwned_4098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_HeapRegion_16] -> ()
d_TraceWritesWithinOwned_4098 = erased
-- Once.CCC.Machine.SMPrimitives.InstrWritesToHeap
d_InstrWritesToHeap_4140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrWritesToHeap_4140 = erased
-- Once.CCC.Machine.SMPrimitives.TraceNoHeapWrites
d_TraceNoHeapWrites_4142 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceNoHeapWrites_4142 = erased
-- Once.CCC.Machine.SMPrimitives.TracePreservesFrame
d_TracePreservesFrame_4202 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TracePreservesFrame_4202 = erased
-- Once.CCC.Machine.SMPrimitives.TracePreservesHeapMem
d_TracePreservesHeapMem_4208 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TracePreservesHeapMem_4208 = erased
-- Once.CCC.Machine.SMPrimitives.trace-no-heap-writes-append
d_trace'45'no'45'heap'45'writes'45'append_4218 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'no'45'heap'45'writes'45'append_4218 v0 ~v1 ~v2 v3
  = du_trace'45'no'45'heap'45'writes'45'append_4218 v0 v3
du_trace'45'no'45'heap'45'writes'45'append_4218 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny
du_trace'45'no'45'heap'45'writes'45'append_4218 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             seq (coe v2)
             (coe
                du_trace'45'no'45'heap'45'writes'45'append_4218 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.NoFrameOp
d_NoFrameOp_4452 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_NoFrameOp_4452 = erased
-- Once.CCC.Machine.SMPrimitives.TraceNoFrameOps
d_TraceNoFrameOps_4454 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_TraceNoFrameOps_4454 = erased
-- Once.CCC.Machine.SMPrimitives.trace-no-frame-ops-append
d_trace'45'no'45'frame'45'ops'45'append_4464 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'no'45'frame'45'ops'45'append_4464 v0 ~v1 v2 v3
  = du_trace'45'no'45'frame'45'ops'45'append_4464 v0 v2 v3
du_trace'45'no'45'frame'45'ops'45'append_4464 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trace'45'no'45'frame'45'ops'45'append_4464 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       du_trace'45'no'45'frame'45'ops'45'append_4464 (coe v4) (coe v6)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-writes-above-append
d_trace'45'writes'45'above'45'append_4488 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'writes'45'above'45'append_4488 ~v0 v1 ~v2 v3 v4
  = du_trace'45'writes'45'above'45'append_4488 v1 v3 v4
du_trace'45'writes'45'above'45'append_4488 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trace'45'writes'45'above'45'append_4488 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_instr'45'writes'45'slot_694 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                       (coe
                          du_trace'45'writes'45'above'45'append_4488 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'writes'45'above'45'append_4488 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-writes-below-append
d_trace'45'writes'45'below'45'append_4544 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'writes'45'below'45'append_4544 ~v0 v1 ~v2 v3 v4
  = du_trace'45'writes'45'below'45'append_4544 v1 v3 v4
du_trace'45'writes'45'below'45'append_4544 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trace'45'writes'45'below'45'append_4544 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_instr'45'writes'45'slot_694 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                       (coe
                          du_trace'45'writes'45'below'45'append_4544 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'writes'45'below'45'append_4544 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-slot-reads-above-append
d_trace'45'slot'45'reads'45'above'45'append_4600 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'slot'45'reads'45'above'45'append_4600 ~v0 v1 ~v2 v3 v4
  = du_trace'45'slot'45'reads'45'above'45'append_4600 v1 v3 v4
du_trace'45'slot'45'reads'45'above'45'append_4600 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trace'45'slot'45'reads'45'above'45'append_4600 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_instr'45'reads'45'slot_700 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                       (coe
                          du_trace'45'slot'45'reads'45'above'45'append_4600 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'slot'45'reads'45'above'45'append_4600 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-slot-reads-below-append
d_trace'45'slot'45'reads'45'below'45'append_4656 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_trace'45'slot'45'reads'45'below'45'append_4656 ~v0 v1 ~v2 v3 v4
  = du_trace'45'slot'45'reads'45'below'45'append_4656 v1 v3 v4
du_trace'45'slot'45'reads'45'below'45'append_4656 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trace'45'slot'45'reads'45'below'45'append_4656 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_instr'45'reads'45'slot_700 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                       (coe
                          du_trace'45'slot'45'reads'45'below'45'append_4656 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'slot'45'reads'45'below'45'append_4656 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-writes-above-mono
d_trace'45'writes'45'above'45'mono_4712 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_trace'45'writes'45'above'45'mono_4712 ~v0 ~v1 v2 v3 v4
  = du_trace'45'writes'45'above'45'mono_4712 v2 v3 v4
du_trace'45'writes'45'above'45'mono_4712 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_trace'45'writes'45'above'45'mono_4712 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> let v5 = d_instr'45'writes'45'slot_694 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                       (coe
                          du_trace'45'writes'45'above'45'mono_4712 (coe v4) (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'writes'45'above'45'mono_4712 (coe v4) (coe v1) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-slot-reads-above-mono
d_trace'45'slot'45'reads'45'above'45'mono_4766 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_trace'45'slot'45'reads'45'above'45'mono_4766 ~v0 ~v1 v2 v3 v4
  = du_trace'45'slot'45'reads'45'above'45'mono_4766 v2 v3 v4
du_trace'45'slot'45'reads'45'above'45'mono_4766 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_trace'45'slot'45'reads'45'above'45'mono_4766 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> let v5 = d_instr'45'reads'45'slot_700 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                       (coe
                          du_trace'45'slot'45'reads'45'above'45'mono_4766 (coe v4) (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'slot'45'reads'45'above'45'mono_4766 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-writes-below-mono
d_trace'45'writes'45'below'45'mono_4820 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_trace'45'writes'45'below'45'mono_4820 ~v0 ~v1 v2 v3 v4
  = du_trace'45'writes'45'below'45'mono_4820 v2 v3 v4
du_trace'45'writes'45'below'45'mono_4820 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_trace'45'writes'45'below'45'mono_4820 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> let v5 = d_instr'45'writes'45'slot_694 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) (coe v1))
                       (coe
                          du_trace'45'writes'45'below'45'mono_4820 (coe v4) (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'writes'45'below'45'mono_4820 (coe v4) (coe v1) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.trace-slot-reads-below-mono
d_trace'45'slot'45'reads'45'below'45'mono_4878 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_trace'45'slot'45'reads'45'below'45'mono_4878 ~v0 ~v1 v2 v3 v4
  = du_trace'45'slot'45'reads'45'below'45'mono_4878 v2 v3 v4
du_trace'45'slot'45'reads'45'below'45'mono_4878 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_trace'45'slot'45'reads'45'below'45'mono_4878 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> let v5 = d_instr'45'reads'45'slot_700 (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) (coe v1))
                       (coe
                          du_trace'45'slot'45'reads'45'below'45'mono_4878 (coe v4) (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_trace'45'slot'45'reads'45'below'45'mono_4878 (coe v4) (coe v1)
                       (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TraceComposition._.exec-trace
d_exec'45'trace_5030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_5030 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.TraceComposition.exec-trace-halted
d_exec'45'trace'45'halted_5102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_5102 = erased
-- Once.CCC.Machine.SMPrimitives.TraceComposition.exec-trace-append
d_exec'45'trace'45'append_5158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append_5158 = erased
-- Once.CCC.Machine.SMPrimitives.TraceComposition.exec-trace-append-state
d_exec'45'trace'45'append'45'state_5238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append'45'state_5238 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc
d_readLoc_5262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_5262 ~v0 = du_readLoc_5262
du_readLoc_5262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_5262
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.writeLoc
d_writeLoc_5270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_5270 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract
d_exec'45'abstract_5318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_5318 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-trace
d_exec'45'trace_5348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_5348 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.LocState-eq
d_LocState'45'eq_5416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LocState'45'eq_5416 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.REFUTABLE-effect-state-only-frame-dep
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_5418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_5418 v0
  = coe
      d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2910 v0
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.case-on-tag-state-next-slot-invariant
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_5420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_5420
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-deterministic
d_exec'45'abstract'45'deterministic_5422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'deterministic_5422 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_5424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_5424 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_5426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_5426 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_5428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_5428 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-same-frame
d_exec'45'abstract'45'same'45'frame_5430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'same'45'frame_5430 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-abstract-state-next-slot-invariant
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_5432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_5432
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-case-dispatch-preserves-frame
d_exec'45'case'45'dispatch'45'preserves'45'frame_5434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'case'45'dispatch'45'preserves'45'frame_5434 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-loop-preserves-frame
d_exec'45'loop'45'preserves'45'frame_5436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'loop'45'preserves'45'frame_5436 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-trace-preserves-frame
d_exec'45'trace'45'preserves'45'frame_5438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'frame_5438 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.loop-state-next-slot-invariant
d_loop'45'state'45'next'45'slot'45'invariant_5440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'state'45'next'45'slot'45'invariant_5440 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.next-slot-update-preserves-frame
d_next'45'slot'45'update'45'preserves'45'frame_5442 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'frame_5442 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.next-slot-update-preserves-heap-ref
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_5444 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_5444 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.store-at-slot-preserves-above
d_store'45'at'45'slot'45'preserves'45'above_5446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'above_5446 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_5448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_5448 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_5450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_5450 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.worklist-push-preserves-stack-slot
d_worklist'45'push'45'preserves'45'stack'45'slot_5452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_worklist'45'push'45'preserves'45'stack'45'slot_5452 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-heapMem-eq
d_readLoc'45'heapMem'45'eq_5456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'heapMem'45'eq_5456 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-heap-stack
d_readLoc'45'writeLoc'45'heap'45'stack_5458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'heap'45'stack_5458 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-same
d_readLoc'45'writeLoc'45'same_5460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'same_5460 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-stack-ancestor
d_readLoc'45'writeLoc'45'stack'45'ancestor_5462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'ancestor_5462 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-stack-heap
d_readLoc'45'writeLoc'45'stack'45'heap_5464 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'heap_5464 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-stack-slot-gt
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_5466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_5466 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.readLoc-writeLoc-stack-slot-lt
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_5468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_5468 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.writeLoc-regs-commute-general
d_writeLoc'45'regs'45'commute'45'general_5470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'general_5470 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.writeLoc-regs-commute-heap
d_writeLoc'45'regs'45'commute'45'heap_5472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'heap_5472 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-trace-append
d_exec'45'trace'45'append_5476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append_5476 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-trace-append-state
d_exec'45'trace'45'append'45'state_5478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append'45'state_5478 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.exec-trace-halted
d_exec'45'trace'45'halted_5480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_5480 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.tnhw-head
d_tnhw'45'head_5520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> T_InstrNoHeapWrite_764
d_tnhw'45'head_5520 ~v0 v1 ~v2 ~v3 = du_tnhw'45'head_5520 v1
du_tnhw'45'head_5520 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_InstrNoHeapWrite_764
du_tnhw'45'head_5520 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240
        -> coe C_nhw'45'mov'45'to'45'output_766
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242
        -> coe C_nhw'45'mov'45'to'45'input_776
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244
        -> coe C_nhw'45'load'45'indirect_778
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2246
        -> coe C_nhw'45'load'45'indirect'45'suc_780
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248 v1
        -> coe C_nhw'45'load'45'from'45'slot_784
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250 v1
        -> coe C_nhw'45'store'45'at'45'slot_788
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 v1
        -> coe C_nhw'45'lea'45'slot_792
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2258 v1
        -> coe C_nhw'45'restore'45'input_796
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260 v1
        -> coe C_nhw'45'instr'45'alloc'45'stack_804
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2262 v1
        -> coe C_nhw'45'instr'45'dealloc'45'stack_808
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2264 v1
        -> coe C_nhw'45'instr'45'reclaim'45'to_812
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2266 v1
        -> coe C_nhw'45'instr'45'push'45'frame_816
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2268
        -> coe C_nhw'45'instr'45'pop'45'frame_818
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2270
        -> coe C_nhw'45'instr'45'call'45'closure_820
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2272 v1
        -> coe C_nhw'45'worklist'45'init_824
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2274 v1
        -> coe C_nhw'45'worklist'45'push_828
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2276 v1
        -> coe C_nhw'45'worklist'45'pop_832
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2278 v1
        -> coe C_nhw'45'worklist'45'check_836
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2284 v1 v2 v3
        -> coe C_nhw'45'instr'45'sigop_844
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2290 v1 v2 v3
        -> coe C_nhw'45'instr'45'load'45'const_852
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2292 v1
        -> coe C_nhw'45'instr'45'load'45'code'45'addr_860
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2294
        -> coe C_nhw'45'instr'45'save'45'closure'45'reg_862
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2296 v1
        -> coe C_nhw'45'instr'45'load'45'tag'45'lit_856
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2300 v1
        -> coe C_nhw'45'instr'45'alloc'45'heap_866
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2304 v1
        -> coe C_nhw'45'instr'45'reg'45'op_770
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2306 v1
        -> coe C_nhw'45'instr'45'ctrl_774
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2308 v1
        -> coe C_nhw'45'lea'45'indexed_800
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.tnhw-tail
d_tnhw'45'tail_5526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  AgdaAny -> AgdaAny
d_tnhw'45'tail_5526 ~v0 v1 ~v2 v3 = du_tnhw'45'tail_5526 v1 v3
du_tnhw'45'tail_5526 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
du_tnhw'45'tail_5526 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-slot-below
d_exec'45'trace'45'preserves'45'slot'45'below_5650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below_5650 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-slot-below-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_5664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_5664
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-slot-above
d_exec'45'trace'45'preserves'45'slot'45'above_6420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above_6420 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-slot-above-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_6434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_6434
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-ancestor
d_exec'45'trace'45'preserves'45'ancestor_7190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor_7190 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-ancestor-nonwrite
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_7204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_7204 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-heap-loc
d_exec'45'trace'45'preserves'45'heap'45'loc_7864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'loc_7864 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-independent
d_exec'45'trace'45'independent_7938
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-independent"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-independent-below
d_exec'45'trace'45'independent'45'below_7954
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-independent-below"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-deterministic
d_exec'45'trace'45'deterministic_7966
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-deterministic"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-heapMem
d_exec'45'trace'45'preserves'45'heapMem_7974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heapMem_7974 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-same-frame
d_exec'45'trace'45'same'45'frame_8036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'same'45'frame_8036 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.InstrPreservesHalted
d_InstrPreservesHalted_8104 a0 a1 = ()
data T_InstrPreservesHalted_8104
  = C_iph'45'mov'45'to'45'output_8106 |
    C_iph'45'instr'45'reg'45'op_8110 | C_iph'45'instr'45'ctrl_8114 |
    C_iph'45'mov'45'to'45'input_8116 |
    C_iph'45'store'45'at'45'slot_8120 | C_iph'45'lea'45'slot_8124 |
    C_iph'45'alloc'45'stack_8128 | C_iph'45'dealloc'45'stack_8132 |
    C_iph'45'reclaim'45'to_8136 | C_iph'45'push'45'frame_8140 |
    C_iph'45'pop'45'frame_8142 | C_iph'45'call'45'closure_8144 |
    C_iph'45'worklist'45'init_8148 | C_iph'45'worklist'45'push_8152 |
    C_iph'45'worklist'45'check_8156 |
    C_iph'45'instr'45'save'45'closure'45'reg_8158
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-abstract-preserves-halted
d_exec'45'abstract'45'preserves'45'halted_8166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InstrPreservesHalted_8104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted_8166 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.TracePreservesHaltedP
d_TracePreservesHaltedP_8288 a0 a1 = ()
data T_TracePreservesHaltedP_8288
  = C_tph'45''91''93'_8290 |
    C_tph'45''8759'_8296 T_InstrPreservesHalted_8104
                         T_TracePreservesHaltedP_8288
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-halted
d_exec'45'trace'45'preserves'45'halted_8304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted_8304 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.tph-++
d_tph'45''43''43'_8340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TracePreservesHaltedP_8288 ->
  T_TracePreservesHaltedP_8288 -> T_TracePreservesHaltedP_8288
d_tph'45''43''43'_8340 ~v0 v1 ~v2 v3 v4
  = du_tph'45''43''43'_8340 v1 v3 v4
du_tph'45''43''43'_8340 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TracePreservesHaltedP_8288 ->
  T_TracePreservesHaltedP_8288 -> T_TracePreservesHaltedP_8288
du_tph'45''43''43'_8340 v0 v1 v2
  = case coe v1 of
      C_tph'45''91''93'_8290 -> coe v2
      C_tph'45''8759'_8296 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    C_tph'45''8759'_8296 v5
                    (coe du_tph'45''43''43'_8340 (coe v8) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.InstrWF
d_InstrWF_8350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrWF_8350 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.load-indirect-twf
d_load'45'indirect'45'twf_8412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_8412 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_load'45'indirect'45'twf_8412 v3 v4 v6
du_load'45'indirect'45'twf_8412 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_8412 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)))
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_8430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_8430 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_load'45'indirect'45'suc'45'twf_8430 v3 v4 v6
du_load'45'indirect'45'suc'45'twf_8430 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_8430 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)))
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.TraceWF
d_TraceWF_8440 a0 a1 a2 a3 = ()
data T_TraceWF_8440
  = C_twf'45''91''93'_8446 |
    C_twf'45''8759'_8456 AgdaAny T_TraceWF_8440
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.sigop-preserves-halted
d_sigop'45'preserves'45'halted_8468
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.sigop-preserves-halted"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.case-on-tag-preserves-halted
d_case'45'on'45'tag'45'preserves'45'halted_8478
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.case-on-tag-preserves-halted"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.loop-preserves-halted
d_loop'45'preserves'45'halted_8486
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TracePrimitives.loop-preserves-halted"
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_8494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_8494 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-preserves-halted-WF
d_exec'45'trace'45'preserves'45'halted'45'WF_8912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted'45'WF_8912 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.twf-++
d_twf'45''43''43'_8952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440 -> T_TraceWF_8440
d_twf'45''43''43'_8952 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_twf'45''43''43'_8952 v1 v6 v7
du_twf'45''43''43'_8952 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TraceWF_8440 -> T_TraceWF_8440 -> T_TraceWF_8440
du_twf'45''43''43'_8952 v0 v1 v2
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v2)
      (:) v3 v4
        -> case coe v1 of
             C_twf'45''8759'_8456 v9 v10
               -> coe
                    C_twf'45''8759'_8456 v9
                    (coe du_twf'45''43''43'_8952 (coe v4) (coe v10) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.twf-++-decomp
d_twf'45''43''43''45'decomp_8994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twf'45''43''43''45'decomp_8994 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_twf'45''43''43''45'decomp_8994 v1 v6
du_twf'45''43''43''45'decomp_8994 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_twf'45''43''43''45'decomp_8994 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_twf'45''91''93'_8446) (coe v1)
      (:) v2 v3
        -> case coe v1 of
             C_twf'45''8759'_8456 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_twf'45''8759'_8456 v8
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_twf'45''43''43''45'decomp_8994 (coe v3) (coe v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_twf'45''43''43''45'decomp_8994 (coe v3) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.InstrWF-frame-eq
d_InstrWF'45'frame'45'eq_9040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_InstrWF'45'frame'45'eq_9040 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_InstrWF'45'frame'45'eq_9040 v1 v6
du_InstrWF'45'frame'45'eq_9040 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny -> AgdaAny
du_InstrWF'45'frame'45'eq_9040 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-abstract-state-frame-eq
d_exec'45'abstract'45'state'45'frame'45'eq_9222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'frame'45'eq_9222 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-state-frame-eq
d_exec'45'trace'45'state'45'frame'45'eq_9654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'state'45'frame'45'eq_9654 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.TraceWF-frame-eq
d_TraceWF'45'frame'45'eq_9720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440
d_TraceWF'45'frame'45'eq_9720 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_TraceWF'45'frame'45'eq_9720 v1 v6
du_TraceWF'45'frame'45'eq_9720 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TraceWF_8440 -> T_TraceWF_8440
du_TraceWF'45'frame'45'eq_9720 v0 v1
  = case coe v1 of
      C_twf'45''91''93'_8446 -> coe C_twf'45''91''93'_8446
      C_twf'45''8759'_8456 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C_twf'45''8759'_8456
                    (coe du_InstrWF'45'frame'45'eq_9040 (coe v8) (coe v6))
                    (coe du_TraceWF'45'frame'45'eq_9720 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.fe-after
d_fe'45'after_9744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe'45'after_9744 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.TraceWF-alloc-eq
d_TraceWF'45'alloc'45'eq_9756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440
d_TraceWF'45'alloc'45'eq_9756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_TraceWF'45'alloc'45'eq_9756 v6
du_TraceWF'45'alloc'45'eq_9756 :: T_TraceWF_8440 -> T_TraceWF_8440
du_TraceWF'45'alloc'45'eq_9756 v0 = coe v0
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-slot-value
d_exec'45'trace'45'slot'45'value_9770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value_9770 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-slot-value-below
d_exec'45'trace'45'slot'45'value'45'below_9802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value'45'below_9802 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.store-at-slot-result
d_store'45'at'45'slot'45'result_9830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'result_9830 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.store-at-slot-halted
d_store'45'at'45'slot'45'halted_9844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'halted_9844 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.store-at-slot-regs
d_store'45'at'45'slot'45'regs_9858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'regs_9858 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.store-at-slot-preserves-other
d_store'45'at'45'slot'45'preserves'45'other_9874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'other_9874 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-abstract-store-at-slot-preserves-input
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_9902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_9902
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-abstract-store-at-slot-preserves-loc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_9920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_9920
  = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-snoc
d_exec'45'trace'45'snoc_9952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc_9952 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-snoc-state
d_exec'45'trace'45'snoc'45'state_9970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc'45'state_9970 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.lea-slot-result
d_lea'45'slot'45'result_9996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'result_9996 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.lea-slot-halted
d_lea'45'slot'45'halted_10010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'halted_10010 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.lea-slot-preserves-mem
d_lea'45'slot'45'preserves'45'mem_10026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'preserves'45'mem_10026 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-final-lea-slot
d_exec'45'trace'45'final'45'lea'45'slot_10044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'slot_10044 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.exec-trace-final-lea-mov-input
d_exec'45'trace'45'final'45'lea'45'mov'45'input_10080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'mov'45'input_10080 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.store-then-preserve
d_store'45'then'45'preserve_10142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'then'45'preserve_10142 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives.prefix-store-preserve
d_prefix'45'store'45'preserve_10216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prefix'45'store'45'preserve_10216 = erased
-- Once.CCC.Machine.SMPrimitives.TracePrimitives._.psp-cons
d_psp'45'cons_10272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_InstrPreservesHalted_8104 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_InstrPreservesHalted_8104 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_psp'45'cons_10272 = erased
-- Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism._.readLoc
d_readLoc_10326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_10326 ~v0 = du_readLoc_10326
du_readLoc_10326 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_10326
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism._.exec-trace
d_exec'45'trace_10412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_10412 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism.exec-trace-output-deterministic
d_exec'45'trace'45'output'45'deterministic_10498
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism.exec-trace-output-deterministic"
-- Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism.mem-deterministic-step
d_mem'45'deterministic'45'step_10518
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism.mem-deterministic-step"
-- Once.CCC.Machine.SMPrimitives.TraceOutputDeterminism.exec-trace-mem-deterministic
d_exec'45'trace'45'mem'45'deterministic_10538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'mem'45'deterministic_10538 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc
d_readLoc_10616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_10616 ~v0 = du_readLoc_10616
du_readLoc_10616 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_10616
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_654
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract
d_exec'45'abstract_10672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_10672 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
      (coe v0)
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace
d_exec'45'trace_10702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_10702 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3230 (coe v0)
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.InstrPreservesHalted
d_InstrPreservesHalted_10770 a0 a1 = ()
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.InstrWF
d_InstrWF_10772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_InstrWF_10772 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.InstrWF-frame-eq
d_InstrWF'45'frame'45'eq_10774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_InstrWF'45'frame'45'eq_10774 ~v0
  = du_InstrWF'45'frame'45'eq_10774
du_InstrWF'45'frame'45'eq_10774 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
du_InstrWF'45'frame'45'eq_10774 v0 v1 v2 v3 v4 v5
  = coe du_InstrWF'45'frame'45'eq_9040 v0 v5
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.TracePreservesHaltedP
d_TracePreservesHaltedP_10776 a0 a1 = ()
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.TraceWF
d_TraceWF_10778 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.TraceWF-alloc-eq
d_TraceWF'45'alloc'45'eq_10780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440
d_TraceWF'45'alloc'45'eq_10780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_TraceWF'45'alloc'45'eq_10780 v6
du_TraceWF'45'alloc'45'eq_10780 :: T_TraceWF_8440 -> T_TraceWF_8440
du_TraceWF'45'alloc'45'eq_10780 v0 = coe v0
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.TraceWF-frame-eq
d_TraceWF'45'frame'45'eq_10782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440
d_TraceWF'45'frame'45'eq_10782 ~v0
  = du_TraceWF'45'frame'45'eq_10782
du_TraceWF'45'frame'45'eq_10782 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440
du_TraceWF'45'frame'45'eq_10782 v0 v1 v2 v3 v4 v5
  = coe du_TraceWF'45'frame'45'eq_9720 v0 v5
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.case-on-tag-preserves-halted
d_case'45'on'45'tag'45'preserves'45'halted_10784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'preserves'45'halted_10784 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-preserves-halted
d_exec'45'abstract'45'preserves'45'halted_10786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InstrPreservesHalted_8104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted_10786 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-preserves-halted-WF
d_exec'45'abstract'45'preserves'45'halted'45'WF_10788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'halted'45'WF_10788 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-state-frame-eq
d_exec'45'abstract'45'state'45'frame'45'eq_10790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'frame'45'eq_10790 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-store-at-slot-preserves-input
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_10792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'input_10792
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-store-at-slot-preserves-loc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_10794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'loc_10794
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-deterministic
d_exec'45'trace'45'deterministic_10796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'deterministic_10796 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-final-lea-mov-input
d_exec'45'trace'45'final'45'lea'45'mov'45'input_10798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'mov'45'input_10798 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-final-lea-slot
d_exec'45'trace'45'final'45'lea'45'slot_10800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'final'45'lea'45'slot_10800 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-independent
d_exec'45'trace'45'independent_10802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'independent_10802 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-independent-below
d_exec'45'trace'45'independent'45'below_10804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'independent'45'below_10804 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-ancestor
d_exec'45'trace'45'preserves'45'ancestor_10806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor_10806 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-ancestor-nonwrite
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_10808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'ancestor'45'nonwrite_10808 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-halted
d_exec'45'trace'45'preserves'45'halted_10810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted_10810 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-halted-WF
d_exec'45'trace'45'preserves'45'halted'45'WF_10812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'halted'45'WF_10812 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-heap-loc
d_exec'45'trace'45'preserves'45'heap'45'loc_10814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'loc_10814 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-heapMem
d_exec'45'trace'45'preserves'45'heapMem_10816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heapMem_10816 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-slot-above
d_exec'45'trace'45'preserves'45'slot'45'above_10818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above_10818 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-slot-above-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_10820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'above'45'nonwrite_10820
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-slot-below
d_exec'45'trace'45'preserves'45'slot'45'below_10822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below_10822 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-slot-below-nonwrite
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_10824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'slot'45'below'45'nonwrite_10824
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-same-frame
d_exec'45'trace'45'same'45'frame_10826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'same'45'frame_10826 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-slot-value
d_exec'45'trace'45'slot'45'value_10828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value_10828 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-slot-value-below
d_exec'45'trace'45'slot'45'value'45'below_10830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'slot'45'value'45'below_10830 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-snoc
d_exec'45'trace'45'snoc_10832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc_10832 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-snoc-state
d_exec'45'trace'45'snoc'45'state_10834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'snoc'45'state_10834 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-state-frame-eq
d_exec'45'trace'45'state'45'frame'45'eq_10836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'state'45'frame'45'eq_10836 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.lea-slot-halted
d_lea'45'slot'45'halted_10870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'halted_10870 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.lea-slot-preserves-mem
d_lea'45'slot'45'preserves'45'mem_10872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'preserves'45'mem_10872 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.lea-slot-result
d_lea'45'slot'45'result_10874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'slot'45'result_10874 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.load-indirect-suc-twf
d_load'45'indirect'45'suc'45'twf_10876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'twf_10876 ~v0
  = du_load'45'indirect'45'suc'45'twf_10876
du_load'45'indirect'45'suc'45'twf_10876 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'twf_10876 v0 v1 v2 v3 v4 v5
  = coe du_load'45'indirect'45'suc'45'twf_8430 v2 v3 v5
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.load-indirect-twf
d_load'45'indirect'45'twf_10878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'twf_10878 ~v0
  = du_load'45'indirect'45'twf_10878
du_load'45'indirect'45'twf_10878 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'twf_10878 v0 v1 v2 v3 v4 v5
  = coe du_load'45'indirect'45'twf_8412 v2 v3 v5
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.loop-preserves-halted
d_loop'45'preserves'45'halted_10880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'preserves'45'halted_10880 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.prefix-store-preserve
d_prefix'45'store'45'preserve_10882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_TracePreservesHaltedP_8288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prefix'45'store'45'preserve_10882 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.sigop-preserves-halted
d_sigop'45'preserves'45'halted_10884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'preserves'45'halted_10884 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-halted
d_store'45'at'45'slot'45'halted_10886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'halted_10886 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-preserves-other
d_store'45'at'45'slot'45'preserves'45'other_10888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'other_10888 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-regs
d_store'45'at'45'slot'45'regs_10890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'regs_10890 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-result
d_store'45'at'45'slot'45'result_10892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'result_10892 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-then-preserve
d_store'45'then'45'preserve_10894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'then'45'preserve_10894 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.tph-++
d_tph'45''43''43'_10896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TracePreservesHaltedP_8288 ->
  T_TracePreservesHaltedP_8288 -> T_TracePreservesHaltedP_8288
d_tph'45''43''43'_10896 ~v0 = du_tph'45''43''43'_10896
du_tph'45''43''43'_10896 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_TracePreservesHaltedP_8288 ->
  T_TracePreservesHaltedP_8288 -> T_TracePreservesHaltedP_8288
du_tph'45''43''43'_10896 v0 v1 v2 v3
  = coe du_tph'45''43''43'_8340 v0 v2 v3
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.twf-++
d_twf'45''43''43'_10902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440 -> T_TraceWF_8440
d_twf'45''43''43'_10902 ~v0 = du_twf'45''43''43'_10902
du_twf'45''43''43'_10902 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> T_TraceWF_8440 -> T_TraceWF_8440
du_twf'45''43''43'_10902 v0 v1 v2 v3 v4 v5 v6
  = coe du_twf'45''43''43'_8952 v0 v5 v6
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.twf-++-decomp
d_twf'45''43''43''45'decomp_10904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twf'45''43''43''45'decomp_10904 ~v0
  = du_twf'45''43''43''45'decomp_10904
du_twf'45''43''43''45'decomp_10904 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_TraceWF_8440 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_twf'45''43''43''45'decomp_10904 v0 v1 v2 v3 v4 v5
  = coe du_twf'45''43''43''45'decomp_8994 v0 v5
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.LocState-eq
d_LocState'45'eq_10958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LocState'45'eq_10958 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.REFUTABLE-effect-state-only-frame-dep
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_10960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  AgdaAny
d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_10960 v0
  = coe
      d_REFUTABLE'45'effect'45'state'45'only'45'frame'45'dep_2910 v0
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.case-on-tag-state-next-slot-invariant
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_10962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'on'45'tag'45'state'45'next'45'slot'45'invariant_10962
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-deterministic
d_exec'45'abstract'45'deterministic_10964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'deterministic_10964 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-preserves-frame
d_exec'45'abstract'45'preserves'45'frame_10966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'frame_10966 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-preserves-heapMem
d_exec'45'abstract'45'preserves'45'heapMem_10968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heapMem_10968 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-preserves-stack-slot
d_exec'45'abstract'45'preserves'45'stack'45'slot_10970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  T_InstrNoHeapWrite_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'stack'45'slot_10970 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-same-frame
d_exec'45'abstract'45'same'45'frame_10972 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'same'45'frame_10972 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-abstract-state-next-slot-invariant
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_10974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'state'45'next'45'slot'45'invariant_10974
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-case-dispatch-preserves-frame
d_exec'45'case'45'dispatch'45'preserves'45'frame_10976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'case'45'dispatch'45'preserves'45'frame_10976 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-loop-preserves-frame
d_exec'45'loop'45'preserves'45'frame_10978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'loop'45'preserves'45'frame_10978 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-frame
d_exec'45'trace'45'preserves'45'frame_10980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'frame_10980 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.loop-state-next-slot-invariant
d_loop'45'state'45'next'45'slot'45'invariant_10982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loop'45'state'45'next'45'slot'45'invariant_10982 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.next-slot-update-preserves-frame
d_next'45'slot'45'update'45'preserves'45'frame_10984 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'frame_10984 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.next-slot-update-preserves-heap-ref
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_10986 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_next'45'slot'45'update'45'preserves'45'heap'45'ref_10986 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-preserves-above
d_store'45'at'45'slot'45'preserves'45'above_10988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'above_10988 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-preserves-ancestor
d_store'45'at'45'slot'45'preserves'45'ancestor_10990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'ancestor_10990 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-at-slot-preserves-below
d_store'45'at'45'slot'45'preserves'45'below_10992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'at'45'slot'45'preserves'45'below_10992 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.worklist-push-preserves-stack-slot
d_worklist'45'push'45'preserves'45'stack'45'slot_10994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_worklist'45'push'45'preserves'45'stack'45'slot_10994 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-heapMem-eq
d_readLoc'45'heapMem'45'eq_10998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'heapMem'45'eq_10998 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-heap-stack
d_readLoc'45'writeLoc'45'heap'45'stack_11000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'heap'45'stack_11000 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-same
d_readLoc'45'writeLoc'45'same_11002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'same_11002 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-stack-ancestor
d_readLoc'45'writeLoc'45'stack'45'ancestor_11004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'ancestor_11004 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-stack-heap
d_readLoc'45'writeLoc'45'stack'45'heap_11006 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'heap_11006 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-stack-slot-gt
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_11008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'gt_11008 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-writeLoc-stack-slot-lt
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_11010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'writeLoc'45'stack'45'slot'45'lt_11010 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.writeLoc-regs-commute-general
d_writeLoc'45'regs'45'commute'45'general_11012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'general_11012 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.writeLoc-regs-commute-heap
d_writeLoc'45'regs'45'commute'45'heap_11014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_Registers_124 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute'45'heap_11014 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-append
d_exec'45'trace'45'append_11018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append_11018 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-append-state
d_exec'45'trace'45'append'45'state_11020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'append'45'state_11020 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-halted
d_exec'45'trace'45'halted_11022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_11022 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.RSFrame
d_RSFrame_11024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_RSFrame_11024 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.passthrough-output-is-input
d_passthrough'45'output'45'is'45'input_11030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'output'45'is'45'input_11030 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.passthrough-preserves-halted
d_passthrough'45'preserves'45'halted_11052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'preserves'45'halted_11052 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_11066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'mem_11066
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.passthrough-mem-preserved
d_passthrough'45'mem'45'preserved_11088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_passthrough'45'mem'45'preserved_11088 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-output-is-input
d_rec'45'scheme'45'output'45'is'45'input_11112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'input_11112 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-halted
d_rec'45'scheme'45'preserves'45'halted_11148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted_11148 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-stores-input
d_rec'45'scheme'45'stores'45'input_11164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input_11164 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-output-is-slot
d_rec'45'scheme'45'output'45'is'45'slot_11202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot_11202 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-halted-3
d_rec'45'scheme'45'preserves'45'halted'45'3_11222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'3_11222 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-stores-input-3
d_rec'45'scheme'45'stores'45'input'45'3_11238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'stores'45'input'45'3_11238 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-slot-below-3
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_11278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'3_11278 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-heap-3
d_rec'45'scheme'45'preserves'45'heap'45'3_11300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'3_11300 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-ancestor-3
d_rec'45'scheme'45'preserves'45'ancestor'45'3_11322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'3_11322 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s1
d_s1_11342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s1_11342 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 = du_s1_11342 v0 v2 v3
du_s1_11342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s1_11342 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc1
d_alloc1_11344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc1_11344 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_alloc1_11344 v0 v2 v3
du_alloc1_11344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc1_11344 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.mov-preserves
d_mov'45'preserves_11346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves_11346 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s1-not-halted
d_s1'45'not'45'halted_11348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s1'45'not'45'halted_11348 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s2
d_s2_11350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s2_11350 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 = du_s2_11350 v0 v1 v2 v3
du_s2_11350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s2_11350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s1_11342 (coe v0) (coe v2) (coe v3))
         (coe du_alloc1_11344 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc2
d_alloc2_11352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc2_11352 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_alloc2_11352 v0 v1 v2 v3
du_alloc2_11352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc2_11352 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s1_11342 (coe v0) (coe v2) (coe v3))
         (coe du_alloc1_11344 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.loc-neq
d_loc'45'neq_11354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_loc'45'neq_11354 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.store-preserves
d_store'45'preserves_11356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'preserves_11356 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s2-not-halted
d_s2'45'not'45'halted_11358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s2'45'not'45'halted_11358 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s3
d_s3_11360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s3_11360 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 = du_s3_11360 v0 v1 v2 v3
du_s3_11360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s3_11360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 (coe v1))
         (coe du_s2_11350 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_alloc2_11352 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.lea-preserves
d_lea'45'preserves_11362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lea'45'preserves_11362 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step1
d_step1_11364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step1_11364 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step2
d_step2_11366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_11366 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step3
d_step3_11368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step3_11368 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.final-state-eq
d_final'45'state'45'eq_11370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_final'45'state'45'eq_11370 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-trace-4
d_rec'45'scheme'45'trace'45'4_11376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
d_rec'45'scheme'45'trace'45'4_11376 ~v0 v1
  = du_rec'45'scheme'45'trace'45'4_11376 v1
du_rec'45'scheme'45'trace'45'4_11376 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238]
du_rec'45'scheme'45'trace'45'4_11376 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2260
         (coe (1 :: Integer)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
               (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2256 (coe v0))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-halted-4
d_rec'45'scheme'45'preserves'45'halted'45'4_11386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'halted'45'4_11386 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-alloc-correct-4
d_rec'45'scheme'45'alloc'45'correct'45'4_11402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'alloc'45'correct'45'4_11402 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-output-is-slot-4
d_rec'45'scheme'45'output'45'is'45'slot'45'4_11440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'output'45'is'45'slot'45'4_11440 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-slot-below-4
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_11472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'slot'45'below'45'4_11472 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-ancestor-4
d_rec'45'scheme'45'preserves'45'ancestor'45'4_11496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'ancestor'45'4_11496 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.rec-scheme-preserves-heap-4
d_rec'45'scheme'45'preserves'45'heap'45'4_11536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'scheme'45'preserves'45'heap'45'4_11536 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-output
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_11556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'output_11556
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_11606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'input_11606
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_11650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'mem_11650
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_11754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'stackMem_11754
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_11794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'heapMem_11794
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-output
d_exec'45'abstract'45'load'45'indirect'45'output_11838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'output_11838 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-preserves-input
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_11888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'input_11888
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-preserves-stackMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_11930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'stackMem_11930
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-preserves-heapMem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_11970 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'heapMem_11970
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_12010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'alloc_12010
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-input-input
d_exec'45'abstract'45'mov'45'to'45'input'45'input_12032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'input_12032 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-stackMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_12042 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'stackMem_12042
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-heapMem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_12052 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'heapMem_12052
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-suc-preserves-alloc
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_12062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'suc'45'preserves'45'alloc_12062
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_12102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'alloc_12102
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-alloc
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_12114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'alloc_12114
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-restore-input-preserves-alloc
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_12144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'alloc_12144
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-output-preserves-alloc
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_12172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'output'45'preserves'45'alloc_12172
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-store-at-slot-preserves-alloc
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_12184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'at'45'slot'45'preserves'45'alloc_12184
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-instr-load-tag-lit-preserves-alloc
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_12198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'instr'45'load'45'tag'45'lit'45'preserves'45'alloc_12198
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-store-indirect-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_12210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'preserves'45'alloc_12210
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-store-indirect-suc-preserves-alloc
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_12232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'store'45'indirect'45'suc'45'preserves'45'alloc_12232
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.restore-trace-preserves-alloc
d_restore'45'trace'45'preserves'45'alloc_12256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'alloc_12256 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-restore-input-sets-input
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_12276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'sets'45'input_12276
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-restore-input-preserves-stackMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_12308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'stackMem_12308
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-restore-input-preserves-heapMem
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_12338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'restore'45'input'45'preserves'45'heapMem_12338
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.restore-trace-preserves-stackMem
d_restore'45'trace'45'preserves'45'stackMem_12368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'stackMem_12368 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.restore-trace-preserves-heapMem
d_restore'45'trace'45'preserves'45'heapMem_12384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restore'45'trace'45'preserves'45'heapMem_12384 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-sets-input
d_setup'45'trace'45'sets'45'input_12408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'sets'45'input_12408 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-preserves-stackMem
d_setup'45'trace'45'preserves'45'stackMem_12444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'stackMem_12444 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-preserves-heapMem
d_setup'45'trace'45'preserves'45'heapMem_12460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'heapMem_12460 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-preserves-alloc
d_setup'45'trace'45'preserves'45'alloc_12476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'alloc_12476 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.load-indirect-suc-halted-success
d_load'45'indirect'45'suc'45'halted'45'success_12490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'suc'45'halted'45'success_12490 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-preserves-halted
d_setup'45'trace'45'preserves'45'halted_12556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'preserves'45'halted_12556 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.setup-trace-exec
d_setup'45'trace'45'exec_12590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_setup'45'trace'45'exec_12590 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-sets-input
d_prod'45'setup'45'trace'45'sets'45'input_12630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'sets'45'input_12630 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-preserves-stackMem
d_prod'45'setup'45'trace'45'preserves'45'stackMem_12666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'stackMem_12666 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-preserves-heapMem
d_prod'45'setup'45'trace'45'preserves'45'heapMem_12682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'heapMem_12682 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-preserves-alloc
d_prod'45'setup'45'trace'45'preserves'45'alloc_12698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'alloc_12698 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.load-indirect-halted-success
d_load'45'indirect'45'halted'45'success_12712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'indirect'45'halted'45'success_12712 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-preserves-halted
d_prod'45'setup'45'trace'45'preserves'45'halted_12778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'preserves'45'halted_12778 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-setup-trace-exec
d_prod'45'setup'45'trace'45'exec_12812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'setup'45'trace'45'exec_12812 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-preserves-heap-ref
d_exec'45'abstract'45'preserves'45'heap'45'ref_12844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'preserves'45'heap'45'ref_12844 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.case-on-tag-trace-preserves-heap-ref
d_case'45'on'45'tag'45'trace'45'preserves'45'heap'45'ref_13146
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.case-on-tag-trace-preserves-heap-ref"
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.loop-trace-preserves-heap-ref
d_loop'45'trace'45'preserves'45'heap'45'ref_13156
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.loop-trace-preserves-heap-ref"
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.REFUTABLE-alloc-heap-trace-preserves-heap-ref
d_REFUTABLE'45'alloc'45'heap'45'trace'45'preserves'45'heap'45'ref_13166
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.REFUTABLE-alloc-heap-trace-preserves-heap-ref"
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-trace-preserves-heap-ref
d_exec'45'trace'45'preserves'45'heap'45'ref_13174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heap'45'ref_13174 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-alloc-helper
d_prod'45'left'45'setup'45'alloc'45'helper_13948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'alloc'45'helper_13948 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.exec-trace-preserves-alloc-4
d_exec'45'trace'45'preserves'45'alloc'45'4_13968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'alloc'45'4_13968 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.step-2
d_step'45'2_13988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'2_13988 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._._.step-3
d_step'45'3_14006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'3_14006 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-halted-helper
d_prod'45'left'45'setup'45'halted'45'helper_14086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'halted'45'helper_14086 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₁
d_s'8321'_14110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8321'_14110 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_s'8321'_14110 v0 v2 v3
du_s'8321'_14110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8321'_14110 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₁
d_alloc'8321'_14112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8321'_14112 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_alloc'8321'_14112 v0 v2 v3
du_alloc'8321'_14112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8321'_14112 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₂
d_s'8322'_14114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8322'_14114 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_s'8322'_14114 v0 v1 v2 v3
du_s'8322'_14114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8322'_14114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s'8321'_14110 (coe v0) (coe v2) (coe v3))
         (coe du_alloc'8321'_14112 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₂
d_alloc'8322'_14116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8322'_14116 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_alloc'8322'_14116 v0 v1 v2 v3
du_alloc'8322'_14116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8322'_14116 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s'8321'_14110 (coe v0) (coe v2) (coe v3))
         (coe du_alloc'8321'_14112 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.rdi-s₂
d_rdi'45's'8322'_14118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45's'8322'_14118 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-s₂
d_readLoc'45's'8322'_14120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45's'8322'_14120 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.left-twf
d_left'45'twf_14122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_TraceWF_8440
d_left'45'twf_14122 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_left'45'twf_14122 v4 v5
du_left'45'twf_14122 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_TraceWF_8440
du_left'45'twf_14122 v0 v1
  = coe
      C_twf'45''8759'_8456 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         C_twf'45''8759'_8456 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            C_twf'45''8759'_8456
            (coe du_load'45'indirect'45'twf_8412 (coe v0) (coe v1) erased)
            (coe
               C_twf'45''8759'_8456 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe C_twf'45''91''93'_8446))))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-input-helper
d_prod'45'left'45'setup'45'input'45'helper_14134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'left'45'setup'45'input'45'helper_14134 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₁
d_s'8321'_14158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8321'_14158 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_s'8321'_14158 v0 v2 v3
du_s'8321'_14158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8321'_14158 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₁
d_alloc'8321'_14160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8321'_14160 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_alloc'8321'_14160 v0 v2 v3
du_alloc'8321'_14160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8321'_14160 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2240)
         (coe v1) (coe v2))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₂
d_s'8322'_14162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8322'_14162 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_s'8322'_14162 v0 v1 v2 v3
du_s'8322'_14162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8322'_14162 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s'8321'_14158 (coe v0) (coe v2) (coe v3))
         (coe du_alloc'8321'_14160 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₂
d_alloc'8322'_14164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8322'_14164 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_alloc'8322'_14164 v0 v1 v2 v3
du_alloc'8322'_14164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8322'_14164 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2250
            (coe v1))
         (coe du_s'8321'_14158 (coe v0) (coe v2) (coe v3))
         (coe du_alloc'8321'_14160 (coe v0) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₃
d_s'8323'_14166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8323'_14166 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_s'8323'_14166 v0 v1 v2 v3
du_s'8323'_14166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8323'_14166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe du_s'8322'_14162 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_alloc'8322'_14164 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₃
d_alloc'8323'_14168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8323'_14168 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_alloc'8323'_14168 v0 v1 v2 v3
du_alloc'8323'_14168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8323'_14168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2244)
         (coe du_s'8322'_14162 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_alloc'8322'_14164 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.rdi-s₂
d_rdi'45's'8322'_14170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45's'8322'_14170 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.readLoc-s₂
d_readLoc'45's'8322'_14172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45's'8322'_14172 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.nh₁
d_nh'8321'_14174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh'8321'_14174 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.nh₂
d_nh'8322'_14176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh'8322'_14176 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.nh₃
d_nh'8323'_14178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nh'8323'_14178 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.decomp
d_decomp_14180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decomp_14180 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-indirect-preserves-mem
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_14190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'indirect'45'preserves'45'mem_14190
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-mov-to-input-preserves-mem
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_14296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'mov'45'to'45'input'45'preserves'45'mem_14296
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-mem-helper
d_prod'45'left'45'setup'45'mem'45'helper_14320
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-mem-helper"
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-saves-input
d_prod'45'left'45'setup'45'saves'45'input_14332
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-left-setup-saves-input"
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-from-slot-preserves-mem
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_14342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'preserves'45'mem_14342
  = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-right-setup-alloc-helper
d_prod'45'right'45'setup'45'alloc'45'helper_14412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'alloc'45'helper_14412 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step-through
d_step'45'through_14432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'through_14432 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.step-2
d_step'45'2_14476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'2_14476 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._._.step-3
d_step'45'3_14492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'3_14492 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-right-setup-mem-helper
d_prod'45'right'45'setup'45'mem'45'helper_14564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'mem'45'helper_14564 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step-through
d_step'45'through_14590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'through_14590 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.s'
d_s''_14624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s''_14624 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_s''_14624 v1
du_s''_14624 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s''_14624 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_426
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_416 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_418 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_420 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_424 (coe v0))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.mem-eq
d_mem'45'eq_14626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'eq_14626 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.nothing-case
d_nothing'45'case_14628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nothing'45'case_14628 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.step-2
d_step'45'2_14658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'2_14658 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._._.step-3
d_step'45'3_14680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'3_14680 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._._._.exec-trace-preserves-stackMem-2
d_exec'45'trace'45'preserves'45'stackMem'45'2_14698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'stackMem'45'2_14698 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._._._.exec-trace-preserves-heapMem-2
d_exec'45'trace'45'preserves'45'heapMem'45'2_14756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'preserves'45'heapMem'45'2_14756 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-right-setup-input-helper
d_prod'45'right'45'setup'45'input'45'helper_14838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'input'45'helper_14838 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.step-2
d_step'45'2_14890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'2_14890 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._._.step-3
d_step'45'3_14912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'3_14912 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.exec-abstract-load-from-slot-output
d_exec'45'abstract'45'load'45'from'45'slot'45'output_14990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'load'45'from'45'slot'45'output_14990 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics.prod-right-setup-halted-helper
d_prod'45'right'45'setup'45'halted'45'helper_15026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'right'45'setup'45'halted'45'helper_15026 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₁
d_s'8321'_15048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8321'_15048 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_s'8321'_15048 v0 v1 v2 v3
du_s'8321'_15048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8321'_15048 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
            (coe v1))
         (coe v2) (coe v3))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₁
d_alloc'8321'_15050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8321'_15050 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_alloc'8321'_15050 v0 v1 v2 v3
du_alloc'8321'_15050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8321'_15050 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2248
            (coe v1))
         (coe v2) (coe v3))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.s₂
d_s'8322'_15052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_s'8322'_15052 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_s'8322'_15052 v0 v1 v2 v3
du_s'8322'_15052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_s'8322'_15052 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
         (coe du_s'8321'_15048 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_alloc'8321'_15050 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.alloc₂
d_alloc'8322'_15054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
d_alloc'8322'_15054 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_alloc'8322'_15054 v0 v1 v2 v3
du_alloc'8322'_15054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492
du_alloc'8322'_15054 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_3228
         (coe v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2242)
         (coe du_s'8321'_15048 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe du_alloc'8321'_15050 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.output-s₁
d_output'45's'8321'_15056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45's'8321'_15056 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.input-s₂
d_input'45's'8322'_15058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45's'8322'_15058 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.snd-s₂
d_snd'45's'8322'_15060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45's'8322'_15060 = erased
-- Once.CCC.Machine.SMPrimitives.RecSchemeSemantics._.right-twf
d_right'45'twf_15062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_492 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_TraceWF_8440
d_right'45'twf_15062 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8
  = du_right'45'twf_15062 v4 v5 v7
du_right'45'twf_15062 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_TraceWF_8440
du_right'45'twf_15062 v0 v1 v2
  = coe
      C_twf'45''8759'_8456
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v0))
         (coe v2))
      (coe
         C_twf'45''8759'_8456 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            C_twf'45''8759'_8456
            (coe
               du_load'45'indirect'45'suc'45'twf_8430 (coe v0) (coe v1) erased)
            (coe
               C_twf'45''8759'_8456 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe C_twf'45''91''93'_8446))))
