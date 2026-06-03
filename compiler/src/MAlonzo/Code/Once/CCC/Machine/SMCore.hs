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

module MAlonzo.Code.Once.CCC.Machine.SMCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Allocator.AbstractInstance
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Machine.SMCore.Slot
d_Slot_16 :: ()
d_Slot_16 = erased
-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_18 = ()
data T_HeapRegion_18
  = C_heap'45'region_28 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
                        Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_24 ::
  T_HeapRegion_18 -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_region'45'ref_24 v0
  = case coe v0 of
      C_heap'45'region_28 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_26 :: T_HeapRegion_18 -> Integer
d_region'45'size_26 v0
  = case coe v0 of
      C_heap'45'region_28 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_30 a0 a1 = ()
newtype T_InRegion_30
  = C_in'45'region_38 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_40 :: ()
d_HeapOwnership_40 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_42 a0 a1 = ()
data T_OutsideOwned_42
  = C_outside'45'nil_46 |
    C_outside'45'cons_54 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                         T_OutsideOwned_42
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_56 = ()
data T_AbstractReg_56 = C_Input1_58 | C_Input2_60 | C_Output_62
-- Once.CCC.Machine.SMCore.ValueLocation
d_ValueLocation_66 a0 = ()
data T_ValueLocation_66
  = C_AtStack_70 AgdaAny Integer |
    C_AtDynamic_72 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_76 a0 = ()
data T_StoredValue_76
  = C_SV'45'Ptr_80 T_ValueLocation_66 | C_SV'45'Tag_82 Integer |
    C_SV'45'Lit_86 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
    C_SV'45'Code_88 Integer
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_66 -> T_ValueLocation_66
d_sucLoc_92 ~v0 v1 = du_sucLoc_92 v1
du_sucLoc_92 :: T_ValueLocation_66 -> T_ValueLocation_66
du_sucLoc_92 v0
  = case coe v0 of
      C_AtStack_70 v1 v2
        -> coe
             C_AtStack_70 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_AtDynamic_72 v1
        -> coe
             C_AtDynamic_72
             (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_66 -> Integer -> T_ValueLocation_66
d_offsetLoc_102 ~v0 v1 v2 = du_offsetLoc_102 v1 v2
du_offsetLoc_102 ::
  T_ValueLocation_66 -> Integer -> T_ValueLocation_66
du_offsetLoc_102 v0 v1
  = case coe v0 of
      C_AtStack_70 v2 v3
        -> coe C_AtStack_70 (coe v2) (coe addInt (coe v1) (coe v3))
      C_AtDynamic_72 v2
        -> coe
             C_AtDynamic_72
             (coe
                MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_98 (coe v2)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_116 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_HeapMem_122 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__130 ::
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__130 v0 v1
  = case coe v0 of
      C_Input1_58
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Input2_60
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_62
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_134 a0 = ()
data T_Registers_134
  = C_mkRegs_154 T_StoredValue_76 T_StoredValue_76 T_StoredValue_76
                 Integer
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_146 :: T_Registers_134 -> T_StoredValue_76
d_input1_146 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_148 :: T_Registers_134 -> T_StoredValue_76
d_input2_148 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_150 :: T_Registers_134 -> T_StoredValue_76
d_output_150 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_152 :: T_Registers_134 -> Integer
d_stackSlot_152 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 -> T_AbstractReg_56 -> T_StoredValue_76
d_readReg_158 ~v0 v1 v2 = du_readReg_158 v1 v2
du_readReg_158 ::
  T_Registers_134 -> T_AbstractReg_56 -> T_StoredValue_76
du_readReg_158 v0 v1
  = case coe v1 of
      C_Input1_58 -> coe d_input1_146 (coe v0)
      C_Input2_60 -> coe d_input2_148 (coe v0)
      C_Output_62 -> coe d_output_150 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 ->
  T_AbstractReg_56 -> T_StoredValue_76 -> T_Registers_134
d_writeReg_168 ~v0 v1 v2 = du_writeReg_168 v1 v2
du_writeReg_168 ::
  T_Registers_134 ->
  T_AbstractReg_56 -> T_StoredValue_76 -> T_Registers_134
du_writeReg_168 v0 v1
  = case coe v1 of
      C_Input1_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe v2) (coe d_input2_148 (coe v0))
                  (coe d_output_150 (coe v0)) (coe d_stackSlot_152 (coe v0)))
      C_Input2_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_146 (coe v0)) (coe v2)
                  (coe d_output_150 (coe v0)) (coe d_stackSlot_152 (coe v0)))
      C_Output_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_146 (coe v0))
                  (coe d_input2_148 (coe v0)) (coe v2)
                  (coe d_stackSlot_152 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 -> Integer -> T_Registers_134
d_writeStackSlot_184 ~v0 v1 v2 = du_writeStackSlot_184 v1 v2
du_writeStackSlot_184 ::
  T_Registers_134 -> Integer -> T_Registers_134
du_writeStackSlot_184 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_146 (coe v0))
      (coe d_input2_148 (coe v0)) (coe d_output_150 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 -> Integer -> T_Registers_134
d_incrStackSlot_192 ~v0 v1 v2 = du_incrStackSlot_192 v1 v2
du_incrStackSlot_192 ::
  T_Registers_134 -> Integer -> T_Registers_134
du_incrStackSlot_192 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_146 (coe v0))
      (coe d_input2_148 (coe v0)) (coe d_output_150 (coe v0))
      (coe addInt (coe d_stackSlot_152 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 -> Integer -> T_Registers_134
d_decrStackSlot_200 ~v0 v1 v2 = du_decrStackSlot_200 v1 v2
du_decrStackSlot_200 ::
  T_Registers_134 -> Integer -> T_Registers_134
du_decrStackSlot_200 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_146 (coe v0))
      (coe d_input2_148 (coe v0)) (coe d_output_150 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_152 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_220 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_296 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_318 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_342 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_364 a0 = ()
data T_LocState_364
  = C_mkLocState_384 T_Registers_134
                     (AgdaAny -> Integer -> Maybe T_StoredValue_76)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_76)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_376 :: T_LocState_364 -> T_Registers_134
d_regs_376 v0
  = case coe v0 of
      C_mkLocState_384 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_378 ::
  T_LocState_364 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_stackMem_378 v0
  = case coe v0 of
      C_mkLocState_384 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_380 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_heapMem_380 v0
  = case coe v0 of
      C_mkLocState_384 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_382 :: T_LocState_364 -> Bool
d_halted_382 v0
  = case coe v0 of
      C_mkLocState_384 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_386 = ()
data T_AllocMode_386 = C_Stack_388 | C_Heap_390
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_394 a0 = ()
data T_AllocState_394 = C_mkAllocState_458 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_452 :: T_AllocState_394 -> AgdaAny
d_current'45'frame_452 v0
  = case coe v0 of
      C_mkAllocState_458 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_454 :: T_AllocState_394 -> Integer
d_next'45'slot_454 v0
  = case coe v0 of
      C_mkAllocState_458 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_456 :: T_AllocState_394 -> Integer
d_next'45'heap'45'ref_456 v0
  = case coe v0 of
      C_mkAllocState_458 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_488 ::
  T_LocState_364 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_readStackLoc_488 v0 v1 v2 = coe d_stackMem_378 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_496 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_readHeapLoc_496 v0 v1 = coe d_heapMem_380 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
d_readLoc_502 ~v0 v1 v2 = du_readLoc_502 v1 v2
du_readLoc_502 ::
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
du_readLoc_502 v0 v1
  = case coe v1 of
      C_AtStack_70 v2 v3 -> coe d_stackMem_378 v0 v2 v3
      C_AtDynamic_72 v2 -> coe d_heapMem_380 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
d_writeStackMem'45'aux_522 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_522 v5 v6 v7 v8
du_writeStackMem'45'aux_522 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
du_writeStackMem'45'aux_522 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
                              else coe seq (coe v7) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem
d_writeStackMem_530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_76) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_writeStackMem_530 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_522
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_writeHeapMem_544 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_544 v1 v2 v3 v4
du_writeHeapMem_544 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
du_writeHeapMem_544 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.Memory.HeapAddress.du_'8799'HL'45'aux_62
              (let v4
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         erased
                         (\ v4 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                              (coe
                                 MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                 (coe
                                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                    (coe v1))))
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               eqInt
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v1)))
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v3))))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  eqInt
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v3)))))) in
               coe
                 (case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                      -> if coe v5
                           then coe
                                  seq (coe v6)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                           else coe
                                  seq (coe v6)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v5)
                                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                    _ -> MAlonzo.RTE.mazUnreachableError))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
                    (coe v3))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                else coe seq (coe v6) (coe v0 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny -> Integer -> T_StoredValue_76 -> T_LocState_364
d_writeLocToStack_574 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_384 (coe d_regs_376 (coe v1))
      (coe
         d_writeStackMem_530 (coe v0) (coe d_stackMem_378 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_380 (coe v1)) (coe d_halted_382 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
d_writeLocToHeap_584 ~v0 v1 v2 v3 = du_writeLocToHeap_584 v1 v2 v3
du_writeLocToHeap_584 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
du_writeLocToHeap_584 v0 v1 v2
  = coe
      C_mkLocState_384 (coe d_regs_376 (coe v0))
      (coe d_stackMem_378 (coe v0))
      (coe
         du_writeHeapMem_544 (coe d_heapMem_380 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_382 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 -> T_StoredValue_76 -> T_LocState_364
d_writeLoc_592 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_70 v4 v5
        -> coe
             d_writeLocToStack_574 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_72 v4
        -> case coe v3 of
             C_SV'45'Ptr_80 v5
               -> case coe v5 of
                    C_AtStack_70 v6 v7 -> coe v1
                    C_AtDynamic_72 v6
                      -> coe du_writeLocToHeap_584 (coe v1) (coe v4) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Tag_82 v5
               -> coe du_writeLocToHeap_584 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_86 v5 v6 v7
               -> coe du_writeLocToHeap_584 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_88 v5
               -> coe du_writeLocToHeap_584 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_638 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_676 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_716 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_716 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_736 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  T_Registers_134 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_736 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_764 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_796 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1036 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1088 a0 = ()
data T_LocSourceExt_1088
  = C_Loc_1092 T_ValueLocation_66 | C_IndReg_1094 T_AbstractReg_56 |
    C_IndRegSuc_1096 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_76 -> Maybe T_ValueLocation_66
d_sv'45'as'45'loc_1100 ~v0 v1 = du_sv'45'as'45'loc_1100 v1
du_sv'45'as'45'loc_1100 ::
  T_StoredValue_76 -> Maybe T_ValueLocation_66
du_sv'45'as'45'loc_1100 v0
  = case coe v0 of
      C_SV'45'Ptr_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_82 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_86 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_88 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_134 -> T_LocSourceExt_1088 -> Maybe T_ValueLocation_66
d_resolveSourceExt_1106 ~v0 v1 v2 = du_resolveSourceExt_1106 v1 v2
du_resolveSourceExt_1106 ::
  T_Registers_134 -> T_LocSourceExt_1088 -> Maybe T_ValueLocation_66
du_resolveSourceExt_1106 v0 v1
  = case coe v1 of
      C_Loc_1092 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1094 v2
        -> coe
             du_sv'45'as'45'loc_1100 (coe du_readReg_158 (coe v0) (coe v2))
      C_IndRegSuc_1096 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1100 (coe du_readReg_158 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_92 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1136 a0 = ()
data T_Instr_1136
  = C_load_1140 T_AbstractReg_56 T_LocSourceExt_1088 |
    C_store_1142 T_LocSourceExt_1088 T_AbstractReg_56 |
    C_mov_1144 T_AbstractReg_56 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1152 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_readHeapLoc_1152 v0 v1 = coe d_heapMem_380 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
d_readLoc_1154 ~v0 = du_readLoc_1154
du_readLoc_1154 ::
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
du_readLoc_1154 = coe du_readLoc_502
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1156 ::
  T_LocState_364 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_readStackLoc_1156 v0 v1 v2 = coe d_stackMem_378 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_writeHeapMem_1158 ~v0 = du_writeHeapMem_1158
du_writeHeapMem_1158 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
du_writeHeapMem_1158 = coe du_writeHeapMem_544
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 -> T_StoredValue_76 -> T_LocState_364
d_writeLoc_1160 v0 = coe d_writeLoc_592 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1162 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1164 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1164 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1166 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1168 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1170 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1172 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1174 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  T_Registers_134 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1174 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
d_writeLocToHeap_1176 ~v0 = du_writeLocToHeap_1176
du_writeLocToHeap_1176 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
du_writeLocToHeap_1176 = coe du_writeLocToHeap_584
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny -> Integer -> T_StoredValue_76 -> T_LocState_364
d_writeLocToStack_1178 v0 = coe d_writeLocToStack_574 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_76) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_writeStackMem_1180 v0 = coe d_writeStackMem_530 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
d_writeStackMem'45'aux_1182 ~v0 = du_writeStackMem'45'aux_1182
du_writeStackMem'45'aux_1182 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
du_writeStackMem'45'aux_1182 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_522 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'with'45'value_1184 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1184 v1 v2
du_exec'45'load'45'with'45'value_1184 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'with'45'value_1184 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_384 (coe du_writeReg_168 (d_regs_376 (coe v3)) v0 v2)
                  (coe d_stackMem_378 (coe v3)) (coe d_heapMem_380 (coe v3))
                  (coe d_halted_382 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_384 (coe d_regs_376 (coe v2))
                  (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'via'45'resolved_1196 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1196 v1 v2
du_exec'45'load'45'via'45'resolved_1196 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'via'45'resolved_1196 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1184 v0
                  (coe du_readLoc_502 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_384 (coe d_regs_376 (coe v2))
                  (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'via'45'resolved_1208 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_592 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_384 (coe d_regs_376 (coe v3))
                  (coe d_stackMem_378 (coe v3)) (coe d_heapMem_380 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'suc'45'via'45'resolved_1218 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1218 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1218 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'suc'45'via'45'resolved_1218 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1184 v0
                  (coe du_readLoc_502 (coe v3) (coe du_sucLoc_92 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_384 (coe d_regs_376 (coe v2))
                  (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'suc'45'via'45'resolved_1230 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_592
                  (coe v0) (coe v4) (coe du_sucLoc_92 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_384 (coe d_regs_376 (coe v3))
                  (coe d_stackMem_378 (coe v3)) (coe d_heapMem_380 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_364 -> T_LocState_364
d_exec_1240 v0 v1
  = case coe v1 of
      C_load_1140 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1196 v2
                  (coe du_resolveSourceExt_1106 (coe d_regs_376 (coe v4)) (coe v3))
                  v4)
      C_store_1142 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1208 v0
                  (coe du_resolveSourceExt_1106 (coe d_regs_376 (coe v4)) (coe v2))
                  (coe du_readReg_158 (coe d_regs_376 (coe v4)) (coe v3)) v4)
      C_mov_1144 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_384
                  (coe
                     du_writeReg_168 (d_regs_376 (coe v4)) v2
                     (coe du_readReg_158 (coe d_regs_376 (coe v4)) (coe v3)))
                  (coe d_stackMem_378 (coe v4)) (coe d_heapMem_380 (coe v4))
                  (coe d_halted_382 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1266 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1272 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_364 -> T_LocState_364
d_execList_1274 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_382 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1274 (coe v0) (coe v4) (coe d_exec_1240 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1306 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_readHeapLoc_1306 v0 v1 = coe d_heapMem_380 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
d_readLoc_1308 ~v0 = du_readLoc_1308
du_readLoc_1308 ::
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
du_readLoc_1308 = coe du_readLoc_502
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1310 ::
  T_LocState_364 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_readStackLoc_1310 v0 v1 v2 = coe d_stackMem_378 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_writeHeapMem_1312 ~v0 = du_writeHeapMem_1312
du_writeHeapMem_1312 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
du_writeHeapMem_1312 = coe du_writeHeapMem_544
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 -> T_StoredValue_76 -> T_LocState_364
d_writeLoc_1314 v0 = coe d_writeLoc_592 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1316 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1318 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1318 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1320 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1322 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1324 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1326 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1328 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  T_Registers_134 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1328 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
d_writeLocToHeap_1330 ~v0 = du_writeLocToHeap_1330
du_writeLocToHeap_1330 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
du_writeLocToHeap_1330 = coe du_writeLocToHeap_584
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny -> Integer -> T_StoredValue_76 -> T_LocState_364
d_writeLocToStack_1332 v0 = coe d_writeLocToStack_574 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_76) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_writeStackMem_1334 v0 = coe d_writeStackMem_530 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
d_writeStackMem'45'aux_1336 ~v0 = du_writeStackMem'45'aux_1336
du_writeStackMem'45'aux_1336 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
du_writeStackMem'45'aux_1336 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_522 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_364 -> T_LocState_364
d_exec_1340 v0 = coe d_exec_1240 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1342 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1344 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'suc'45'via'45'resolved_1346 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1346
du_exec'45'load'45'suc'45'via'45'resolved_1346 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'suc'45'via'45'resolved_1346
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1218
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'via'45'resolved_1348 ~v0
  = du_exec'45'load'45'via'45'resolved_1348
du_exec'45'load'45'via'45'resolved_1348 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'via'45'resolved_1348
  = coe du_exec'45'load'45'via'45'resolved_1196
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'with'45'value_1350 ~v0
  = du_exec'45'load'45'with'45'value_1350
du_exec'45'load'45'with'45'value_1350 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'with'45'value_1350
  = coe du_exec'45'load'45'with'45'value_1184
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'suc'45'via'45'resolved_1352 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1230 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'via'45'resolved_1354 v0
  = coe d_exec'45'store'45'via'45'resolved_1208 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_364 -> T_LocState_364
d_execList_1356 v0 = coe d_execList_1274 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_76
d_resolved'45'readLoc_1358 ~v0 v1 v2
  = du_resolved'45'readLoc_1358 v1 v2
du_resolved'45'readLoc_1358 ::
  T_LocState_364 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_76
du_resolved'45'readLoc_1358 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1106 (coe d_regs_376 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_502 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1388 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1458 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1534 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1564 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1620 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1672 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1724 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1740 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1758 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1772 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1790 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1856 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1880 = erased
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1908 = ()
data T_AbstractInstr_1908
  = C_mov'45'to'45'output_1910 | C_mov'45'to'45'input_1912 |
    C_mov'45'output'45'to'45'input2_1914 |
    C_mov'45'input2'45'to'45'output_1916 | C_load'45'indirect_1918 |
    C_load'45'indirect'45'suc_1920 |
    C_load'45'from'45'slot_1922 Integer |
    C_store'45'at'45'slot_1924 Integer | C_store'45'indirect_1926 |
    C_store'45'indirect'45'suc_1928 | C_lea'45'slot_1930 Integer |
    C_restore'45'input_1932 Integer |
    C_instr'45'alloc'45'stack_1934 Integer |
    C_instr'45'dealloc'45'stack_1936 Integer |
    C_instr'45'reclaim'45'to_1938 Integer |
    C_instr'45'push'45'frame_1940 Integer |
    C_instr'45'pop'45'frame_1942 | C_instr'45'call'45'closure_1944 |
    C_worklist'45'init_1946 Integer | C_worklist'45'push_1948 Integer |
    C_worklist'45'pop_1950 Integer | C_worklist'45'check_1952 Integer |
    C_instr'45'sigop_1958 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 |
    C_instr'45'load'45'const_1962 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
    C_instr'45'load'45'code'45'addr_1964 Integer |
    C_instr'45'save'45'closure'45'reg_1966 |
    C_instr'45'load'45'tag'45'lit_1968 Integer |
    C_instr'45'case'45'on'45'tag_1970 [T_AbstractInstr_1908]
                                      [T_AbstractInstr_1908] |
    C_instr'45'alloc'45'heap_1972 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1974 :: ()
d_AbstractTrace_1974 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_1976 = ()
data T_TreeTrace_1976
  = C_ε_1978 | C_instr_1980 T_AbstractInstr_1908 |
    C__'9656'__1982 T_TreeTrace_1976 T_TreeTrace_1976 |
    C_branch_1984 Integer T_TreeTrace_1976 T_TreeTrace_1976 |
    C_call'45'sub_1986 T_TreeTrace_1976 |
    C_flat_1988 [T_AbstractInstr_1908]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_1990 :: [T_AbstractInstr_1908] -> T_TreeTrace_1976
d_flatToTree_1990 v0
  = case coe v0 of
      [] -> coe C_ε_1978
      (:) v1 v2
        -> coe
             C__'9656'__1982 (coe C_instr_1980 (coe v1))
             (coe d_flatToTree_1990 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_1996 :: T_TreeTrace_1976 -> [T_AbstractInstr_1908]
d_treeToFlat_1996 v0
  = case coe v0 of
      C_ε_1978 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1980 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1982 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1996 (coe v1)) (coe d_treeToFlat_1996 (coe v2))
      C_branch_1984 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1996 (coe v2)) (coe d_treeToFlat_1996 (coe v3))
      C_call'45'sub_1986 v1 -> coe d_treeToFlat_1996 (coe v1)
      C_flat_1988 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2012 ::
  Integer -> T_TreeTrace_1976 -> [T_AbstractInstr_1908]
d_treeToRunnable_2012 v0 v1
  = case coe v1 of
      C_ε_1978 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1980 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1982 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2012 (coe v0) (coe v2))
             (coe d_treeToRunnable_2012 (coe v0) (coe v3))
      C_branch_1984 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2012 (coe v0) (coe v3))
             (coe d_treeToRunnable_2012 (coe v0) (coe v4))
      C_call'45'sub_1986 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1948 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2012 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1950 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_1988 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2042 ::
  Integer -> T_TreeTrace_1976 -> [T_AbstractInstr_1908]
d_treeToRunnableWithInit_2042 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1946 (coe v0))
      (coe d_treeToRunnable_2012 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2078 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_readHeapLoc_2078 v0 v1 = coe d_heapMem_380 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
d_readLoc_2080 ~v0 = du_readLoc_2080
du_readLoc_2080 ::
  T_LocState_364 -> T_ValueLocation_66 -> Maybe T_StoredValue_76
du_readLoc_2080 = coe du_readLoc_502
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2082 ::
  T_LocState_364 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_readStackLoc_2082 v0 v1 v2 = coe d_stackMem_378 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
d_writeHeapMem_2084 ~v0 = du_writeHeapMem_2084
du_writeHeapMem_2084 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_76) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_76
du_writeHeapMem_2084 = coe du_writeHeapMem_544
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 -> T_StoredValue_76 -> T_LocState_364
d_writeLoc_2086 v0 = coe d_writeLoc_592 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2088 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2090 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2090 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2092 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2094 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2096 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2098 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2100 ::
  T_LocState_364 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 ->
  T_Registers_134 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2100 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
d_writeLocToHeap_2102 ~v0 = du_writeLocToHeap_2102
du_writeLocToHeap_2102 ::
  T_LocState_364 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_76 -> T_LocState_364
du_writeLocToHeap_2102 = coe du_writeLocToHeap_584
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  AgdaAny -> Integer -> T_StoredValue_76 -> T_LocState_364
d_writeLocToStack_2104 v0 = coe d_writeLocToStack_574 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_76) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_76 -> AgdaAny -> Integer -> Maybe T_StoredValue_76
d_writeStackMem_2106 v0 = coe d_writeStackMem_530 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
d_writeStackMem'45'aux_2108 ~v0 = du_writeStackMem'45'aux_2108
du_writeStackMem'45'aux_2108 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_76 ->
  T_StoredValue_76 -> Maybe T_StoredValue_76
du_writeStackMem'45'aux_2108 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_522 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_364 -> T_LocState_364
d_exec_2112 v0 = coe d_exec_1240 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2114 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2116 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'suc'45'via'45'resolved_2118 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2118
du_exec'45'load'45'suc'45'via'45'resolved_2118 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'suc'45'via'45'resolved_2118
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1218
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'via'45'resolved_2120 ~v0
  = du_exec'45'load'45'via'45'resolved_2120
du_exec'45'load'45'via'45'resolved_2120 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_66 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'via'45'resolved_2120
  = coe du_exec'45'load'45'via'45'resolved_1196
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'load'45'with'45'value_2122 ~v0
  = du_exec'45'load'45'with'45'value_2122
du_exec'45'load'45'with'45'value_2122 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
du_exec'45'load'45'with'45'value_2122
  = coe du_exec'45'load'45'with'45'value_1184
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'suc'45'via'45'resolved_2124 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1230 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_66 ->
  T_StoredValue_76 -> T_LocState_364 -> T_LocState_364
d_exec'45'store'45'via'45'resolved_2126 v0
  = coe d_exec'45'store'45'via'45'resolved_1208 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_364 -> T_LocState_364
d_execList_2128 v0 = coe d_execList_1274 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2132 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2134 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2136 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2138 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2140 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_AbstractReg_56 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2142 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2144 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_66 ->
  T_LocState_364 ->
  T_StoredValue_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2146 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2148 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2150 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2152 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2154 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 ->
  T_LocState_364 ->
  T_ValueLocation_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2156 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_76
d_resolved'45'readLoc_2158 ~v0 = du_resolved'45'readLoc_2158
du_resolved'45'readLoc_2158 ::
  T_LocState_364 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_76
du_resolved'45'readLoc_2158 = coe du_resolved'45'readLoc_1358
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2160 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2160 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2160 ::
  Maybe T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2160 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe du_writeReg_168 (d_regs_376 (coe v1)) (coe C_Output_62) v3)
                (coe d_stackMem_378 (coe v1)) (coe d_heapMem_380 (coe v1))
                (coe d_halted_382 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384 (coe d_regs_376 (coe v1))
                (coe d_stackMem_378 (coe v1)) (coe d_heapMem_380 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2172 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2172 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2172 ::
  Maybe T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2172 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe du_writeReg_168 (d_regs_376 (coe v1)) (coe C_Input1_58) v3)
                (coe d_stackMem_378 (coe v1)) (coe d_heapMem_380 (coe v1))
                (coe d_halted_382 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384 (coe d_regs_376 (coe v1))
                (coe d_stackMem_378 (coe v1)) (coe d_heapMem_380 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2190 ::
  T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2190 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2196 ::
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2196 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2204 ::
  T_StoredValue_76 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2204 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2210 ::
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2210 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_76
d_unit'45'storedvalue_2212 ~v0 = du_unit'45'storedvalue_2212
du_unit'45'storedvalue_2212 :: T_StoredValue_76
du_unit'45'storedvalue_2212
  = coe
      C_SV'45'Lit_86 (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_190) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2218
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_364 -> T_StoredValue_76
d_pure'45'sigop'45'output_2224 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_196 (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
           -> coe du_unit'45'storedvalue_2212
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe d_structured'45'pure'45'sigop'45'output_2218 v0 v1 v2 v3 v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_364 -> T_StoredValue_76
d_exec'45'sigop'45'output'45'of_2258 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_266
        -> coe
             d_pure'45'sigop'45'output_2224 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_268
        -> coe du_unit'45'storedvalue_2212
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_270
        -> coe du_unit'45'storedvalue_2212
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_364 -> T_StoredValue_76
d_exec'45'sigop'45'output_2268 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2258 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_296 (coe v3))
      (coe v3) (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_364 -> Bool
d_exec'45'sigop'45'halts'45'of_2278 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2278 v3
du_exec'45'sigop'45'halts'45'of_2278 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 -> Bool
du_exec'45'sigop'45'halts'45'of_2278 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_270
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_364 -> Bool
d_exec'45'sigop'45'halts_2284 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2284 v3
du_exec'45'sigop'45'halts_2284 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 -> Bool
du_exec'45'sigop'45'halts_2284 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2278
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_296 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1908 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2290 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1910
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input1_58)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1912
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Input1_58)
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_1914
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Input2_60)
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_1916
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input2_60)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_load'45'indirect_1918
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1196 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1100
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_1920
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1218 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1100
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_1922 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2160
             (coe
                du_readLoc_502 (coe v2)
                (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1924 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_592 (coe v0) (coe v2)
                (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4))
                (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_store'45'indirect_1926
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1208 v0
                (coe
                   du_sv'45'as'45'loc_1100
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_1928
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1230 v0
                (coe
                   du_sv'45'as'45'loc_1100
                   (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_lea'45'slot_1930 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_80
                      (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4))))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_restore'45'input_1932 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2172
             (coe
                du_readLoc_502 (coe v2)
                (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1934 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe du_incrStackSlot_192 (coe d_regs_376 (coe v2)) (coe v4))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe
                C_mkAllocState_458 (coe d_current'45'frame_452 (coe v3))
                (coe addInt (coe d_next'45'slot_454 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_456 (coe v3)))
      C_instr'45'dealloc'45'stack_1936 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe du_decrStackSlot_200 (coe d_regs_376 (coe v2)) (coe v4))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1938 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_458 (coe d_current'45'frame_452 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_456 (coe v3)))
      C_instr'45'push'45'frame_1940 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeStackSlot_184 (coe d_regs_376 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1942
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1944
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1946 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1948 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_592 (coe v0) (coe v2)
                (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4))
                (coe du_readReg_158 (coe d_regs_376 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_worklist'45'pop_1950 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2160
             (coe
                du_readLoc_502 (coe v2)
                (coe C_AtStack_70 (coe d_current'45'frame_452 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1952 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_1958 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (d_exec'45'sigop'45'output_2268
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe du_exec'45'sigop'45'halts_2284 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_1962 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Lit_86 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_1964 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Code_88 (coe v4)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_1966
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_1968 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Tag_82 (coe v4)))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_1970 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384 (coe d_regs_376 (coe v2))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v3)
      C_instr'45'alloc'45'heap_1972 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_384
                (coe
                   du_writeReg_168 (d_regs_376 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_80
                      (coe
                         C_AtDynamic_72
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_456 (coe v3)))))))
                (coe d_stackMem_378 (coe v2)) (coe d_heapMem_380 (coe v2))
                (coe d_halted_382 (coe v2)))
             (coe
                C_mkAllocState_458 (coe d_current'45'frame_452 (coe v3))
                (coe d_next'45'slot_454 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_456 (coe v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1908] ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2292 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_382 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2292 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2290 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2290 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1908 ->
  [T_AbstractInstr_1908] ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2504 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1908 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2550 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_364 -> T_AllocState_394 -> Integer -> Maybe Integer
d_getTag_2584 ~v0 v1 v2 v3 = du_getTag_2584 v1 v2 v3
du_getTag_2584 ::
  T_LocState_364 -> T_AllocState_394 -> Integer -> Maybe Integer
du_getTag_2584 v0 v1 v2
  = let v3
          = coe d_stackMem_378 v0 (d_current'45'frame_452 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1976 ->
  T_LocState_364 ->
  T_AllocState_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2608 v0 v1 v2 v3
  = case coe v1 of
      C_ε_1978
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_1980 v4
        -> let v5 = d_halted_382 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2290 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__1982 v4 v5
        -> let v6 = d_halted_382 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2608 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2608 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2608 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_1984 v4 v5 v6
        -> let v7 = d_halted_382 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_378 v2 (d_current'45'frame_452 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2608 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2608 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2608 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2608 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2608 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_1986 v4
        -> let v5 = d_halted_382 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2608 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_1988 v4
        -> coe d_exec'45'trace_2292 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2768 ::
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2768 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1976 ->
  T_TreeTrace_1976 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2786 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1908 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2832 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1976 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2872 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1908] ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2912 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1908] ->
  [T_AbstractInstr_1908] ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2932 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2990
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1976 ->
  T_LocState_364 ->
  T_AllocState_394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2998 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2998
du_exec'45'tree'45'flat'45'equiv'45'simple_2998 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2998
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
