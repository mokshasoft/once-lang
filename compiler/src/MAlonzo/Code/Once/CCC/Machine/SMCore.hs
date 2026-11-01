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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Allocator.AbstractInstance
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.Contract
import qualified MAlonzo.Code.Once.IR.Semantics.Event
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_16 = ()
data T_HeapRegion_16
  = C_heap'45'region_26 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
                        Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_22 ::
  T_HeapRegion_16 -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_region'45'ref_22 v0
  = case coe v0 of
      C_heap'45'region_26 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_24 :: T_HeapRegion_16 -> Integer
d_region'45'size_24 v0
  = case coe v0 of
      C_heap'45'region_26 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_28 a0 a1 = ()
newtype T_InRegion_28
  = C_in'45'region_36 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_38 :: ()
d_HeapOwnership_38 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_40 a0 a1 = ()
data T_OutsideOwned_40
  = C_outside'45'nil_44 |
    C_outside'45'cons_52 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                         T_OutsideOwned_40
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_54 = ()
data T_AbstractReg_54 = C_Input1_56 | C_Output_58
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_62 a0 = ()
data T_StoredValue_62
  = C_SV'45'Ptr_66 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_SV'45'Tag_68 Integer |
    C_SV'45'Lit_72 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Type.T_FitsInReg_24 AgdaAny |
    C_SV'45'Code_74 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_78 ~v0 v1 = du_sucLoc_78 v1
du_sucLoc_78 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_78 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v1 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v1
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
             (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_offsetLoc_88 ~v0 v1 v2 = du_offsetLoc_88 v1 v2
du_offsetLoc_88 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_offsetLoc_88 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 (coe v2)
             (coe addInt (coe v1) (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
             (coe
                MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_90 (coe v2)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_102 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_HeapMem_108 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__112 ::
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__112 v0 v1
  = case coe v0 of
      C_Input1_56
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_58
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_116 a0 = ()
data T_Registers_116
  = C_mkRegs_128 T_StoredValue_62 T_StoredValue_62
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_124 :: T_Registers_116 -> T_StoredValue_62
d_input1_124 v0
  = case coe v0 of
      C_mkRegs_128 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_126 :: T_Registers_116 -> T_StoredValue_62
d_output_126 v0
  = case coe v0 of
      C_mkRegs_128 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 -> T_AbstractReg_54 -> T_StoredValue_62
d_readReg_132 ~v0 v1 v2 = du_readReg_132 v1 v2
du_readReg_132 ::
  T_Registers_116 -> T_AbstractReg_54 -> T_StoredValue_62
du_readReg_132 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_124 (coe v0)
      C_Output_58 -> coe d_output_126 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_AbstractReg_54 -> T_StoredValue_62 -> T_Registers_116
d_writeReg_140 ~v0 v1 v2 = du_writeReg_140 v1 v2
du_writeReg_140 ::
  T_Registers_116 ->
  T_AbstractReg_54 -> T_StoredValue_62 -> T_Registers_116
du_writeReg_140 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 -> coe C_mkRegs_128 (coe v2) (coe d_output_126 (coe v0)))
      C_Output_58
        -> coe
             (\ v2 -> coe C_mkRegs_128 (coe d_input1_124 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_164 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_206 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_226 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_240 = ()
data T_RegOp_240 = C_out'45'nz_242
-- Once.CCC.Machine.SMCore.sv-nz
d_sv'45'nz_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 -> T_StoredValue_62
d_sv'45'nz_246 ~v0 v1 = du_sv'45'nz_246 v1
du_sv'45'nz_246 :: T_StoredValue_62 -> T_StoredValue_62
du_sv'45'nz_246 v0
  = case coe v0 of
      C_SV'45'Ptr_66 v1 -> coe C_SV'45'Tag_68 (coe (1 :: Integer))
      C_SV'45'Tag_68 v1
        -> coe
             C_SV'45'Tag_68
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe eqInt (coe v1) (coe (0 :: Integer))) (coe (0 :: Integer))
                (coe (1 :: Integer)))
      C_SV'45'Lit_72 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    C_SV'45'Tag_68
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe eqInt (coe v3) (coe (0 :: Integer))) (coe (0 :: Integer))
                       (coe (1 :: Integer)))
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe C_SV'45'Tag_68 (coe (1 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_SV'45'Code_74 v1 -> coe C_SV'45'Tag_68 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState
d_LocState_254 a0 = ()
data T_LocState_254
  = C_mkLocState_286 T_Registers_116
                     (AgdaAny -> Integer -> Maybe T_StoredValue_62)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
                      Maybe T_StoredValue_62)
                     Bool [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] Bool
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_272 :: T_LocState_254 -> T_Registers_116
d_regs_272 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_274 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_stackMem_274 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_276 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_heapMem_276 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_278 :: T_LocState_254 -> Bool
d_halted_278 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.ev-log
d_ev'45'log_280 ::
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_ev'45'log_280 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.left
d_left_282 :: T_LocState_254 -> Bool
d_left_282 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.faulted
d_faulted_284 :: T_LocState_254 -> Bool
d_faulted_284 v0
  = case coe v0 of
      C_mkLocState_286 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ending
d_ending_290 ::
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ending_290 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_left_282 (coe v0)) (coe d_faulted_284 (coe v0))
-- Once.CCC.Machine.SMCore.setReg
d_setReg_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_240 -> T_Registers_116 -> T_Registers_116
d_setReg_296 ~v0 ~v1 v2 = du_setReg_296 v2
du_setReg_296 :: T_Registers_116 -> T_Registers_116
du_setReg_296 v0
  = coe
      du_writeReg_140 v0 (coe C_Output_58)
      (coe
         du_sv'45'nz_246 (coe du_readReg_132 (coe v0) (coe C_Output_58)))
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_240 -> T_LocState_254 -> T_LocState_254
d_exec'45'reg'45'op_302 ~v0 ~v1 v2 = du_exec'45'reg'45'op_302 v2
du_exec'45'reg'45'op_302 :: T_LocState_254 -> T_LocState_254
du_exec'45'reg'45'op_302 v0
  = coe
      C_mkLocState_286 (coe du_setReg_296 (coe d_regs_272 (coe v0)))
      (coe d_stackMem_274 (coe v0)) (coe d_heapMem_276 (coe v0))
      (coe d_halted_278 (coe v0)) (coe d_ev'45'log_280 (coe v0))
      (coe d_left_282 (coe v0)) (coe d_faulted_284 (coe v0))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_308 = ()
data T_AllocMode_308 = C_Stack_310 | C_Heap_312
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_320 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_320 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_320 v0 v1 v3 v4
du_size'45'with'45'aux_320 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_320 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_336 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_336 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_320 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_348 a0 = ()
data T_AllocState_348
  = C_mkAllocState_460 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_448 :: T_AllocState_348 -> AgdaAny
d_current'45'frame_448 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_450 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_450 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_452 :: T_AllocState_348 -> Integer
d_frame'45'slots_452 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_454 :: T_AllocState_348 -> Integer
d_next'45'slot_454 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_456 :: T_AllocState_348 -> Integer
d_next'45'heap'45'ref_456 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_458 :: T_AllocState_348 -> Integer -> Integer
d_block'45'size_458 v0
  = case coe v0 of
      C_mkAllocState_460 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_508 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_508 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_516 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_516 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_522 ~v0 v1 v2 = du_readLoc_522 v1 v2
du_readLoc_522 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_522 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_274 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_276 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_542 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_542 v5 v6 v7 v8
du_writeStackMem'45'aux_542 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_542 v0 v1 v2 v3
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
d_writeStackMem_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_550 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_542
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_572 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_572 v5 v6 v7
du_clear'45'frame'45'aux_572 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_572 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              else coe seq (coe v6) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.clear-frame
d_clear'45'frame_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_578 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_572
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_602 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_654 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_654 v3 v4 v5
du_writeHeapMem'45'aux_654 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_654 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_660 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_660 v1 v2 v3 v4
du_writeHeapMem_660 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_660 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_654
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__72 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_670 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_286 (coe d_regs_272 (coe v1))
      (coe
         d_writeStackMem_550 (coe v0) (coe d_stackMem_274 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_276 (coe v1)) (coe d_halted_278 (coe v1))
      (coe d_ev'45'log_280 (coe v1)) (coe d_left_282 (coe v1))
      (coe d_faulted_284 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_680 ~v0 v1 v2 v3 = du_writeLocToHeap_680 v1 v2 v3
du_writeLocToHeap_680 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_680 v0 v1 v2
  = coe
      C_mkLocState_286 (coe d_regs_272 (coe v0))
      (coe d_stackMem_274 (coe v0))
      (coe
         du_writeHeapMem_660 (coe d_heapMem_276 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_278 (coe v0)) (coe d_ev'45'log_280 (coe v0))
      (coe d_left_282 (coe v0)) (coe d_faulted_284 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_688 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_670 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_66 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_680 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_68 v5
               -> coe du_writeLocToHeap_680 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_72 v5 v6 v7
               -> coe du_writeLocToHeap_680 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_74 v5
               -> coe du_writeLocToHeap_680 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_738 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_776 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_816 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_816 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_836 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_836 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_864 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_896 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1174 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1226 a0 = ()
data T_LocSourceExt_1226
  = C_Loc_1230 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1232 T_AbstractReg_54 | C_IndRegSuc_1234 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1238 ~v0 v1 = du_sv'45'as'45'loc_1238 v1
du_sv'45'as'45'loc_1238 ::
  T_StoredValue_62 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1238 v0
  = case coe v0 of
      C_SV'45'Ptr_66 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_68 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_72 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_LocSourceExt_1226 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1244 ~v0 v1 v2 = du_resolveSourceExt_1244 v1 v2
du_resolveSourceExt_1244 ::
  T_Registers_116 ->
  T_LocSourceExt_1226 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1244 v0 v1
  = case coe v1 of
      C_Loc_1230 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1232 v2
        -> coe
             du_sv'45'as'45'loc_1238 (coe du_readReg_132 (coe v0) (coe v2))
      C_IndRegSuc_1234 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1238 (coe du_readReg_132 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_78 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1274 a0 = ()
data T_Instr_1274
  = C_load_1278 T_AbstractReg_54 T_LocSourceExt_1226 |
    C_store_1280 T_LocSourceExt_1226 T_AbstractReg_54 |
    C_mov_1282 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1290 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1292 ~v0 = du_clear'45'frame'45'aux_1292
du_clear'45'frame'45'aux_1292 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1292 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1294 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1296 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1296 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1298 ~v0 = du_readLoc_1298
du_readLoc_1298 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1298 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1300 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1300 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1302 ~v0 = du_writeHeapMem_1302
du_writeHeapMem_1302 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1302 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1304 ~v0 = du_writeHeapMem'45'aux_1304
du_writeHeapMem'45'aux_1304 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1304 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1306 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1308 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1310 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1310 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1312 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1314 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1316 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1318 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1320 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1320 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1322 ~v0 = du_writeLocToHeap_1322
du_writeLocToHeap_1322 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1322 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1324 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1326 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1328 ~v0 = du_writeStackMem'45'aux_1328
du_writeStackMem'45'aux_1328 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1328 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1330 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1330 v1 v2
du_exec'45'load'45'with'45'value_1330 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1330 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_286 (coe du_writeReg_140 (d_regs_272 (coe v3)) v0 v2)
                  (coe d_stackMem_274 (coe v3)) (coe d_heapMem_276 (coe v3))
                  (coe d_halted_278 (coe v3)) (coe d_ev'45'log_280 (coe v3))
                  (coe d_left_282 (coe v3)) (coe d_faulted_284 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v2))
                  (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v2)) (coe d_left_282 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1342 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1342 v1 v2
du_exec'45'load'45'via'45'resolved_1342 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1342 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1330 v0
                  (coe du_readLoc_522 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v2))
                  (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v2)) (coe d_left_282 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1354 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_688 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v3))
                  (coe d_stackMem_274 (coe v3)) (coe d_heapMem_276 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v3)) (coe d_left_282 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1364 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1364 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1364 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1364 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1330 v0
                  (coe du_readLoc_522 (coe v3) (coe du_sucLoc_78 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v2))
                  (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v2)) (coe d_left_282 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1376 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_688
                  (coe v0) (coe v4) (coe du_sucLoc_78 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v3))
                  (coe d_stackMem_274 (coe v3)) (coe d_heapMem_276 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v3)) (coe d_left_282 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_1386 v0 v1
  = case coe v1 of
      C_load_1278 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1342 v2
                  (coe du_resolveSourceExt_1244 (coe d_regs_272 (coe v4)) (coe v3))
                  v4)
      C_store_1280 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1354 v0
                  (coe du_resolveSourceExt_1244 (coe d_regs_272 (coe v4)) (coe v2))
                  (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe v3)) v4)
      C_mov_1282 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_286
                  (coe
                     du_writeReg_140 (d_regs_272 (coe v4)) v2
                     (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe v3)))
                  (coe d_stackMem_274 (coe v4)) (coe d_heapMem_276 (coe v4))
                  (coe d_halted_278 (coe v4)) (coe d_ev'45'log_280 (coe v4))
                  (coe d_left_282 (coe v4)) (coe d_faulted_284 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1412 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1418 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_1420 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1420 (coe v0) (coe v4) (coe d_exec_1386 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1452 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1454 ~v0 = du_clear'45'frame'45'aux_1454
du_clear'45'frame'45'aux_1454 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1454 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1456 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1458 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1458 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1460 ~v0 = du_readLoc_1460
du_readLoc_1460 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1460 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1462 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1462 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1464 ~v0 = du_writeHeapMem_1464
du_writeHeapMem_1464 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1464 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1466 ~v0 = du_writeHeapMem'45'aux_1466
du_writeHeapMem'45'aux_1466 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1466 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1468 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1470 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1472 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1472 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1474 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1476 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1478 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1480 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1482 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1482 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1484 ~v0 = du_writeLocToHeap_1484
du_writeLocToHeap_1484 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1484 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1486 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1488 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1490 ~v0 = du_writeStackMem'45'aux_1490
du_writeStackMem'45'aux_1490 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1490 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_1494 v0 = coe d_exec_1386 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1496 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1498 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1500 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1500
du_exec'45'load'45'suc'45'via'45'resolved_1500 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1500
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1364
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1502 ~v0
  = du_exec'45'load'45'via'45'resolved_1502
du_exec'45'load'45'via'45'resolved_1502 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1502
  = coe du_exec'45'load'45'via'45'resolved_1342
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1504 ~v0
  = du_exec'45'load'45'with'45'value_1504
du_exec'45'load'45'with'45'value_1504 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1504
  = coe du_exec'45'load'45'with'45'value_1330
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1506 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1376 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1508 v0
  = coe d_exec'45'store'45'via'45'resolved_1354 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_1510 v0 = coe d_execList_1420 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_LocSourceExt_1226 -> Maybe T_StoredValue_62
d_resolved'45'readLoc_1512 ~v0 v1 v2
  = du_resolved'45'readLoc_1512 v1 v2
du_resolved'45'readLoc_1512 ::
  T_LocState_254 -> T_LocSourceExt_1226 -> Maybe T_StoredValue_62
du_resolved'45'readLoc_1512 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1244 (coe d_regs_272 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_522 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1542 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1612 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1688 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1718 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1774 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1826 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1878 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1894 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1912 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1926 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1944 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2010 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2034 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2062 = ()
data T_FlatCtrl_2062
  = C_c'45'label_2064 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2066 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2068 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'entry_2070 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                      Integer |
    C_c'45'ret_2072 Integer |
    C_c'45'call'45'fn_2074 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_c'45'start_2076 Integer | C_c'45'leave_2078
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2086 = ()
data T_AbstractInstr_2086
  = C_mov'45'to'45'output_2088 | C_mov'45'to'45'input_2090 |
    C_load'45'indirect_2092 | C_load'45'indirect'45'suc_2094 |
    C_load'45'from'45'slot_2096 Integer |
    C_store'45'at'45'slot_2098 Integer | C_store'45'indirect_2100 |
    C_store'45'indirect'45'suc_2102 | C_lea'45'slot_2104 Integer |
    C_restore'45'input_2106 Integer |
    C_instr'45'alloc'45'stack_2108 Integer |
    C_instr'45'dealloc'45'stack_2110 Integer |
    C_instr'45'reclaim'45'to_2112 Integer |
    C_instr'45'push'45'frame_2114 Integer |
    C_instr'45'pop'45'frame_2116 | C_instr'45'call'45'closure_2118 |
    C_worklist'45'init_2120 Integer | C_worklist'45'push_2122 Integer |
    C_worklist'45'pop_2124 Integer | C_worklist'45'check_2126 Integer |
    C_instr'45'sigop_2132 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 |
    C_instr'45'load'45'const_2138 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                  MAlonzo.Code.Once.Type.T_FitsInReg_24 AgdaAny |
    C_instr'45'load'45'code'45'addr_2140 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2142 |
    C_instr'45'load'45'tag'45'lit_2144 Integer |
    C_instr'45'alloc'45'heap_2146 Integer | C_instr'45'reg'45'op_2148 |
    C_instr'45'ctrl_2150 T_FlatCtrl_2062
-- Once.CCC.Machine.SMCore.CallI
d_CallI_2152 :: T_AbstractInstr_2086 -> ()
d_CallI_2152 = erased
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2154 :: ()
d_AbstractTrace_2154 = erased
-- Once.CCC.Machine.SMCore.CompUnit
d_CompUnit_2156 = ()
data T_CompUnit_2156
  = C_unit_2170 Integer [T_AbstractInstr_2086]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Machine.SMCore.CompUnit.entry-budget
d_entry'45'budget_2164 :: T_CompUnit_2156 -> Integer
d_entry'45'budget_2164 v0
  = case coe v0 of
      C_unit_2170 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.entry
d_entry_2166 :: T_CompUnit_2156 -> [T_AbstractInstr_2086]
d_entry_2166 v0
  = case coe v0 of
      C_unit_2170 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.blocks
d_blocks_2168 ::
  T_CompUnit_2156 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2168 v0
  = case coe v0 of
      C_unit_2170 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.block-layout
d_block'45'layout_2172 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_AbstractInstr_2086]
d_block'45'layout_2172 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_instr'45'ctrl_2150
                       (coe
                          C_c'45'entry_2070
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_instr'45'ctrl_2150 (coe C_c'45'ret_2072 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout
d_blocks'45'layout_2180 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_AbstractInstr_2086]
d_blocks'45'layout_2180 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_block'45'layout_2172 (coe v1))
             (coe d_blocks'45'layout_2180 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout-++
d_blocks'45'layout'45''43''43'_2190 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blocks'45'layout'45''43''43'_2190 = erased
-- Once.CCC.Machine.SMCore.link
d_link_2202 :: T_CompUnit_2156 -> [T_AbstractInstr_2086]
d_link_2202 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2166 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2150
            (coe C_c'45'ret_2072 (coe d_entry'45'budget_2164 (coe v0))))
         (coe d_blocks'45'layout_2180 (coe d_blocks_2168 (coe v0))))
-- Once.CCC.Machine.SMCore.link-top
d_link'45'top_2206 :: T_CompUnit_2156 -> [T_AbstractInstr_2086]
d_link'45'top_2206 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2166 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe C_instr'45'ctrl_2150 (coe C_c'45'leave_2078))
         (coe d_blocks'45'layout_2180 (coe d_blocks_2168 (coe v0))))
-- Once.CCC.Machine.SMCore.link-pre
d_link'45'pre_2210 ::
  T_CompUnit_2156 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> [T_AbstractInstr_2086]
d_link'45'pre_2210 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2166 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2150
            (coe C_c'45'ret_2072 (coe d_entry'45'budget_2164 (coe v0))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_blocks'45'layout_2180 (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  C_instr'45'ctrl_2150
                  (coe
                     C_c'45'entry_2070
                     (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
                     (coe v3)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMCore.link-post
d_link'45'post_2220 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [T_AbstractInstr_2086]
d_link'45'post_2220 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_instr'45'ctrl_2150 (coe C_c'45'ret_2072 (coe v1)))
      (coe d_blocks'45'layout_2180 (coe v0))
-- Once.CCC.Machine.SMCore.link-block-split
d_link'45'block'45'split_2238 ::
  T_CompUnit_2156 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2086] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_link'45'block'45'split_2238 = erased
-- Once.CCC.Machine.SMCore._.inner
d_inner_2258 ::
  T_CompUnit_2156 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2086] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_2258 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2266 = ()
data T_TreeTrace_2266
  = C_ε_2268 | C_instr_2270 T_AbstractInstr_2086 |
    C__'9656'__2272 T_TreeTrace_2266 T_TreeTrace_2266 |
    C_branch_2274 Integer T_TreeTrace_2266 T_TreeTrace_2266 |
    C_call'45'sub_2276 T_TreeTrace_2266 |
    C_flat_2278 [T_AbstractInstr_2086]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2280 :: [T_AbstractInstr_2086] -> T_TreeTrace_2266
d_flatToTree_2280 v0
  = case coe v0 of
      [] -> coe C_ε_2268
      (:) v1 v2
        -> coe
             C__'9656'__2272 (coe C_instr_2270 (coe v1))
             (coe d_flatToTree_2280 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2286 :: T_TreeTrace_2266 -> [T_AbstractInstr_2086]
d_treeToFlat_2286 v0
  = case coe v0 of
      C_ε_2268 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2270 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2272 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2286 (coe v1)) (coe d_treeToFlat_2286 (coe v2))
      C_branch_2274 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2286 (coe v2)) (coe d_treeToFlat_2286 (coe v3))
      C_call'45'sub_2276 v1 -> coe d_treeToFlat_2286 (coe v1)
      C_flat_2278 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2302 ::
  Integer -> T_TreeTrace_2266 -> [T_AbstractInstr_2086]
d_treeToRunnable_2302 v0 v1
  = case coe v1 of
      C_ε_2268 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2270 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2272 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2302 (coe v0) (coe v2))
             (coe d_treeToRunnable_2302 (coe v0) (coe v3))
      C_branch_2274 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2302 (coe v0) (coe v3))
             (coe d_treeToRunnable_2302 (coe v0) (coe v4))
      C_call'45'sub_2276 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2122 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2302 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2124 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2278 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2332 ::
  Integer -> T_TreeTrace_2266 -> [T_AbstractInstr_2086]
d_treeToRunnableWithInit_2332 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2120 (coe v0))
      (coe d_treeToRunnable_2302 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_2386 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_2388 ~v0 = du_clear'45'frame'45'aux_2388
du_clear'45'frame'45'aux_2388 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_2388 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2390 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2392 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_2392 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_2394 ~v0 = du_readLoc_2394
du_readLoc_2394 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_2394 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2396 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_2396 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_2398 ~v0 = du_writeHeapMem_2398
du_writeHeapMem_2398 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_2398 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_2400 ~v0 = du_writeHeapMem'45'aux_2400
du_writeHeapMem'45'aux_2400 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_2400 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_2402 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2404 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2406 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2406 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2408 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2410 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2412 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2414 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2416 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2416 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_2418 ~v0 = du_writeLocToHeap_2418
du_writeLocToHeap_2418 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_2418 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_2420 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_2422 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_2424 ~v0 = du_writeStackMem'45'aux_2424
du_writeStackMem'45'aux_2424 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_2424 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_2428 v0 = coe d_exec_1386 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2430 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2432 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_2434 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2434
du_exec'45'load'45'suc'45'via'45'resolved_2434 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_2434
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1364
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_2436 ~v0
  = du_exec'45'load'45'via'45'resolved_2436
du_exec'45'load'45'via'45'resolved_2436 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_2436
  = coe du_exec'45'load'45'via'45'resolved_1342
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_2438 ~v0
  = du_exec'45'load'45'with'45'value_2438
du_exec'45'load'45'with'45'value_2438 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_2438
  = coe du_exec'45'load'45'with'45'value_1330
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_2440 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1376 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_2442 v0
  = coe d_exec'45'store'45'via'45'resolved_1354 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_2444 v0 = coe d_execList_1420 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2446 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2446 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2446 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2446 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe du_writeReg_140 (d_regs_272 (coe v1)) (coe C_Output_58) v3)
                (coe d_stackMem_274 (coe v1)) (coe d_heapMem_276 (coe v1))
                (coe d_halted_278 (coe v1)) (coe d_ev'45'log_280 (coe v1))
                (coe d_left_282 (coe v1)) (coe d_faulted_284 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286 (coe d_regs_272 (coe v1))
                (coe d_stackMem_274 (coe v1)) (coe d_heapMem_276 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_280 (coe v1)) (coe d_left_282 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2458 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2458 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2458 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2458 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe du_writeReg_140 (d_regs_272 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_274 (coe v1)) (coe d_heapMem_276 (coe v1))
                (coe d_halted_278 (coe v1)) (coe d_ev'45'log_280 (coe v1))
                (coe d_left_282 (coe v1)) (coe d_faulted_284 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286 (coe d_regs_272 (coe v1))
                (coe d_stackMem_274 (coe v1)) (coe d_heapMem_276 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_280 (coe v1)) (coe d_left_282 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2476 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2476 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2482 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2482 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2490 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2490 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2496 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2496 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62
d_unit'45'storedvalue_2498 ~v0 = du_unit'45'storedvalue_2498
du_unit'45'storedvalue_2498 :: T_StoredValue_62
du_unit'45'storedvalue_2498
  = coe
      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2504 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2504 v3 v4
du_combine'45'typed_2504 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2504 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-int
d_readTyped'45'int_2510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'int_2510 ~v0 v1 = du_readTyped'45'int_2510 v1
du_readTyped'45'int_2510 :: Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'int_2510 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_SV'45'Ptr_66 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_68 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_72 v2 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_fits'45'int_26
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                    MAlonzo.Code.Once.Type.C_fits'45'float_28
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Code_74 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-float
d_readTyped'45'float_2514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'float_2514 ~v0 v1 = du_readTyped'45'float_2514 v1
du_readTyped'45'float_2514 ::
  Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'float_2514 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_SV'45'Ptr_66 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_68 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_72 v2 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_fits'45'int_26
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_fits'45'float_28
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Code_74 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-cell
d_readTyped'45'cell_2520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
d_readTyped'45'cell_2520 ~v0 ~v1 v2 v3 v4
  = du_readTyped'45'cell_2520 v2 v3 v4
du_readTyped'45'cell_2520 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
du_readTyped'45'cell_2520 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             C_SV'45'Ptr_66 v4 -> coe v0 v4
             C_SV'45'Tag_68 v4 -> coe v1 v3
             C_SV'45'Lit_72 v4 v5 v6 -> coe v1 v3
             C_SV'45'Code_74 v4 -> coe v1 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-pair
d_readTyped'45'pair_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_2556 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_readTyped'45'pair_2556 v3 v4 v5 v6 v7 v8
du_readTyped'45'pair_2556 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2556 v0 v1 v2 v3 v4 v5
  = coe
      du_combine'45'typed_2504
      (coe du_readTyped'45'cell_2520 (coe v0) (coe v2) (coe v4))
      (coe du_readTyped'45'cell_2520 (coe v1) (coe v3) (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
d_readReg'45'typed_2572 ~v0 v1 v2 = du_readReg'45'typed_2572 v1 v2
du_readReg'45'typed_2572 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
du_readReg'45'typed_2572 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> case coe v1 of
                C_SV'45'Lit_72 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_26
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> case coe v1 of
                C_SV'45'Lit_72 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_28
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-sum
d_readTyped'45'sum_2582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_2582 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'sum_2582 v3 v4 v5 v6
du_readTyped'45'sum_2582 ::
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_2582 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             C_SV'45'Ptr_66 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_68 v5
               -> case coe v5 of
                    0 -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38) (coe v0 v3)
                    1 -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42) (coe v1 v3)
                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_72 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Code_74 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_2628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
d_readTyped_2628 ~v0 v1 v2 v3 = du_readTyped_2628 v1 v2 v3
du_readTyped_2628 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
du_readTyped_2628 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
           -> coe
                du_readTyped'45'pair_2556
                (coe (\ v6 -> coe du_readTyped_2628 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2628 (coe v5) (coe v6) (coe v2)))
                (coe du_readReg'45'typed_2572 (coe v4))
                (coe du_readReg'45'typed_2572 (coe v5))
                (coe du_readLoc_522 (coe v2) (coe v1))
                (coe du_readLoc_522 (coe v2) (coe du_sucLoc_78 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
           -> coe
                du_readTyped'45'sum_2582
                (coe
                   du_readTyped'45'cell_2520
                   (coe (\ v6 -> coe du_readTyped_2628 (coe v4) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2572 (coe v4)))
                (coe
                   du_readTyped'45'cell_2520
                   (coe (\ v6 -> coe du_readTyped_2628 (coe v5) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2572 (coe v5)))
                (coe du_readLoc_522 (coe v2) (coe v1))
                (coe du_readLoc_522 (coe v2) (coe du_sucLoc_78 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> coe
                du_readTyped'45'int_2510 (coe du_readLoc_522 (coe v2) (coe v1))
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> coe
                du_readTyped'45'float_2514 (coe du_readLoc_522 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2674
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.decode-at
d_decode'45'at_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
d_decode'45'at_2678 ~v0 v1 v2 v3 v4
  = du_decode'45'at_2678 v1 v2 v3 v4
du_decode'45'at_2678 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
du_decode'45'at_2678 v0 v1 v2 v3
  = let v4
          = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v2 of
                 C_SV'45'Ptr_66 v5
                   -> coe du_readTyped_2628 (coe v0) (coe v5) (coe v3)
                 _ -> coe v4) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
           -> case coe v2 of
                C_SV'45'Lit_72 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_26
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
           -> case coe v2 of
                C_SV'45'Lit_72 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_28
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.events-at-arg
d_events'45'at'45'arg_2694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_events'45'at'45'arg_2694 ~v0 v1 ~v2 v3 v4
  = du_events'45'at'45'arg_2694 v1 v3 v4
du_events'45'at'45'arg_2694 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_events'45'at'45'arg_2694 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.IR.Semantics.Event.C_mk'45'event_76
                (MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v1)) v0 v3)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.machine-events
d_machine'45'events_2708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_machine'45'events_2708 ~v0 v1 ~v2 v3 v4
  = du_machine'45'events_2708 v1 v3 v4
du_machine'45'events_2708 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_machine'45'events_2708 v0 v1 v2
  = coe
      du_events'45'at'45'arg_2694 (coe v0) (coe v1)
      (coe
         du_decode'45'at_2678 (coe v0)
         (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v1))
         (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))
         (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_2720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> T_StoredValue_62
d_call'45'sigop'45'ans'45'at_2720 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             C_SV'45'Lit_72 (coe v2) (coe v5)
             (coe
                MAlonzo.Code.Once.IR.Semantics.Trace.d_answer_208
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_134 (coe v0))
                (d_ev'45'log_280 (coe v4))
                (coe
                   MAlonzo.Code.Once.IR.Semantics.Trace.C_callOp_76
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3)) (coe v1)
                   (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3)) (coe v2))
                v6 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2498
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_2750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_StoredValue_62
d_call'45'sigop'45'ans_2750 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           d_call'45'sigop'45'ans'45'at_2720 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v9)
                           (coe
                              du_decode'45'at_2678 (coe v1)
                              (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3))
                              (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56))
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v8) (coe du_unit'45'storedvalue_2498)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_2772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_2772 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Contract.d__'8712'K'63'__106
      (MAlonzo.Code.Once.IR.Semantics.Trace.d_callKey_180
         (coe
            MAlonzo.Code.Once.IR.Semantics.Trace.C_callOp_76
            (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3)) (coe v1)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3)) (coe v2)))
      (MAlonzo.Code.Once.IR.Semantics.Trace.d_calls_196
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_134 (coe v0)))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-val
d_call'45'sigop'45'val_2784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 -> T_StoredValue_62
d_call'45'sigop'45'val_2784 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_call'45'sigop'45'ans_2750 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe
                d_call'45'sigop'45'dec_2772 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2498
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_call'45'sigop'45'output_2800 v0 v1 v2 v3 v4
  = coe
      d_call'45'sigop'45'val_2784 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_pure'45'sigop'45'output_2812 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2842 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
      (coe
         du_sv'45'as'45'loc_1238
         (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny -> T_StoredValue_62
d_pure'45'sigop'45'out'45'val_2818 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_res'45'sv_2822 (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_206 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_182 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                   (coe v0))
                v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2498
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.res-sv
d_res'45'sv_2822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
d_res'45'sv_2822 ~v0 v1 v2 v3 = du_res'45'sv_2822 v1 v2 v3
du_res'45'sv_2822 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
du_res'45'sv_2822 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe du_unit'45'storedvalue_2498
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe C_SV'45'Lit_72 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62
d_pure'45'sigop'45'out'45'aux_2842 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    d_pure'45'sigop'45'out'45'val_2818 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe du_readTyped_2628 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    d_pure'45'sigop'45'out'45'val_2818 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2572 (coe v1)
                       (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2674 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output'45'of_2878 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             d_pure'45'sigop'45'output_2812 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_unit'45'storedvalue_2498
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_unit'45'storedvalue_2498
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             d_call'45'sigop'45'output_2800 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_2892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events'45'of_2892 ~v0 v1 ~v2 v3 v4 v5
  = du_sigop'45'events'45'of_2892 v1 v3 v4 v5
du_sigop'45'events'45'of_2892 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events'45'of_2892 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_machine'45'events_2708 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_machine'45'events_2708 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe du_machine'45'events_2708 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events
d_sigop'45'events_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events_2910 ~v0 v1 ~v2 v3 v4
  = du_sigop'45'events_2910 v1 v3 v4
du_sigop'45'events_2910 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events_2910 v0 v1 v2
  = coe
      du_sigop'45'events'45'of_2892 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output_2920 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2878 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts'45'of_2930 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2930 v3
du_exec'45'sigop'45'halts'45'of_2930 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 -> Bool
du_exec'45'sigop'45'halts'45'of_2930 v0
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts_2936 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2936 v3
du_exec'45'sigop'45'halts_2936 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 -> Bool
du_exec'45'sigop'45'halts_2936 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2930
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.lit-value
d_lit'45'value_2946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
d_lit'45'value_2946 v0 ~v1 v2 v3 = du_lit'45'value_2946 v0 v2 v3
du_lit'45'value_2946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
du_lit'45'value_2946 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_fits'45'int_26
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
             (coe
                mulInt (coe (8 :: Integer))
                (coe
                   MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_116 (coe v0)))
             (coe v2)
      MAlonzo.Code.Once.Type.C_fits'45'float_28
        -> coe
             MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
             (coe
                MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_132
                (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2086 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2952 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2088
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2090
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_load'45'indirect_2092
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1342 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1364 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2096 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2446
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2098 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_688 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2100
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1354 v0
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2102
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1376 v0
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2104 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_66
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_448 (coe v3)) (coe v4))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_restore'45'input_2106 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2458
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2108 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'dealloc'45'stack_2110 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2112 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'push'45'frame_2114 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2116
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2120 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2122 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_688 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2124 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2446
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2126 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2132 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_2920
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe du_exec'45'sigop'45'halts_2936 (coe v6))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_ev'45'log_280 (coe v2))
                   (coe du_sigop'45'events_2910 (coe v4) (coe v6) (coe v2)))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'load'45'const_2138 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_72 (coe v4) (coe v5)
                      (coe du_lit'45'value_2946 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2140 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Code_74 (coe v4)))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2142
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2144 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Tag_68 (coe v4)))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'alloc'45'heap_2146 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_66
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_456 (coe v3)))))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe
                C_mkAllocState_460 (coe d_current'45'frame_448 (coe v3))
                (coe d_saved'45'frames_450 (coe v3))
                (coe d_frame'45'slots_452 (coe v3))
                (coe d_next'45'slot_454 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_456 (coe v3)))))
                (coe
                   d_size'45'with_336 (coe v4)
                   (coe d_next'45'heap'45'ref_456 (coe v3))
                   (coe d_block'45'size_458 (coe v3))))
      C_instr'45'reg'45'op_2148
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_302 (coe v2)) (coe v3)
      C_instr'45'ctrl_2150 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2086] ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2954 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_278 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2954 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2952 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2952 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2086 ->
  [T_AbstractInstr_2086] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3160 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2086 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3206 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
d_getTag_3240 ~v0 v1 v2 v3 = du_getTag_3240 v1 v2 v3
du_getTag_3240 ::
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
du_getTag_3240 v0 v1 v2
  = let v3
          = coe d_stackMem_274 v0 (d_current'45'frame_448 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2266 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3264 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2268
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2270 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2952 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2272 v4 v5
        -> let v6 = d_halted_278 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3264 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3264 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3264 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2274 v4 v5 v6
        -> let v7 = d_halted_278 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_274 v2 (d_current'45'frame_448 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3264 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3264 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3264 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3264 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3264 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2276 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3264 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2278 v4
        -> coe d_exec'45'trace_2954 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3424 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3424 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2266 ->
  T_TreeTrace_2266 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3442 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2086 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3488 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2266 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3528 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2086] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3568 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2266 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3582 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3582
du_exec'45'tree'45'flat'45'equiv'45'simple_3582 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3582
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
