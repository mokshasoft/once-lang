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
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.IR.Semantics.Boundary
import qualified MAlonzo.Code.Once.IR.Semantics.Event
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
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
  = C_mkAllocState_464 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer) (Integer -> Bool)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_450 :: T_AllocState_348 -> AgdaAny
d_current'45'frame_450 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_452 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_452 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_454 :: T_AllocState_348 -> Integer
d_frame'45'slots_454 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_456 :: T_AllocState_348 -> Integer
d_next'45'slot_456 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_458 :: T_AllocState_348 -> Integer
d_next'45'heap'45'ref_458 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_460 :: T_AllocState_348 -> Integer -> Integer
d_block'45'size_460 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.freed
d_freed_462 :: T_AllocState_348 -> Integer -> Bool
d_freed_462 v0
  = case coe v0 of
      C_mkAllocState_464 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_512 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_512 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_520 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_520 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_526 ~v0 v1 v2 = du_readLoc_526 v1 v2
du_readLoc_526 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_526 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_274 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_276 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_546 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_546 v5 v6 v7 v8
du_writeStackMem'45'aux_546 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_546 v0 v1 v2 v3
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
d_writeStackMem_554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_554 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_546
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_576 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_576 v5 v6 v7
du_clear'45'frame'45'aux_576 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_576 v0 v1 v2
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
d_clear'45'frame_582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_582 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_576
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_606 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_658 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_658 v3 v4 v5
du_writeHeapMem'45'aux_658 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_658 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_664 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_664 v1 v2 v3 v4
du_writeHeapMem_664 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_664 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_658
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__72 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.clearBlock-aux
d_clearBlock'45'aux_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clearBlock'45'aux_678 ~v0 ~v1 ~v2 v3 v4
  = du_clearBlock'45'aux_678 v3 v4
du_clearBlock'45'aux_678 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clearBlock'45'aux_678 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             else coe seq (coe v3) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.clearBlock
d_clearBlock_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_clearBlock_682 ~v0 v1 v2 v3 = du_clearBlock_682 v1 v2 v3
du_clearBlock_682 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_clearBlock_682 v0 v1 v2
  = coe
      du_clearBlock'45'aux_678
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44 (coe v2)))
         (coe v1))
      (coe v0 v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_690 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_286 (coe d_regs_272 (coe v1))
      (coe
         d_writeStackMem_554 (coe v0) (coe d_stackMem_274 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_276 (coe v1)) (coe d_halted_278 (coe v1))
      (coe d_ev'45'log_280 (coe v1)) (coe d_left_282 (coe v1))
      (coe d_faulted_284 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_700 ~v0 v1 v2 v3 = du_writeLocToHeap_700 v1 v2 v3
du_writeLocToHeap_700 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_700 v0 v1 v2
  = coe
      C_mkLocState_286 (coe d_regs_272 (coe v0))
      (coe d_stackMem_274 (coe v0))
      (coe
         du_writeHeapMem_664 (coe d_heapMem_276 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_278 (coe v0)) (coe d_ev'45'log_280 (coe v0))
      (coe d_left_282 (coe v0)) (coe d_faulted_284 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_708 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_690 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_66 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_700 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_68 v5
               -> coe du_writeLocToHeap_700 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_72 v5 v6 v7
               -> coe du_writeLocToHeap_700 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_74 v5
               -> coe du_writeLocToHeap_700 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_758 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_796 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_836 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_836 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_856 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_856 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_884 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_884 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_916 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1194 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1246 a0 = ()
data T_LocSourceExt_1246
  = C_Loc_1250 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1252 T_AbstractReg_54 | C_IndRegSuc_1254 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1258 ~v0 v1 = du_sv'45'as'45'loc_1258 v1
du_sv'45'as'45'loc_1258 ::
  T_StoredValue_62 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1258 v0
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
d_resolveSourceExt_1264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_116 ->
  T_LocSourceExt_1246 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1264 ~v0 v1 v2 = du_resolveSourceExt_1264 v1 v2
du_resolveSourceExt_1264 ::
  T_Registers_116 ->
  T_LocSourceExt_1246 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1264 v0 v1
  = case coe v1 of
      C_Loc_1250 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1252 v2
        -> coe
             du_sv'45'as'45'loc_1258 (coe du_readReg_132 (coe v0) (coe v2))
      C_IndRegSuc_1254 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1258 (coe du_readReg_132 (coe v0) (coe v2)) in
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
d_Instr_1294 a0 = ()
data T_Instr_1294
  = C_load_1298 T_AbstractReg_54 T_LocSourceExt_1246 |
    C_store_1300 T_LocSourceExt_1246 T_AbstractReg_54 |
    C_mov_1302 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.win-pick
d_win'45'pick_1306 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> Bool -> Bool
d_win'45'pick_1306 ~v0 v1 v2 v3 = du_win'45'pick_1306 v1 v2 v3
du_win'45'pick_1306 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> Bool -> Bool
du_win'45'pick_1306 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1) (coe v2))
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1322 v0 = coe d_clear'45'frame_582 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1324 ~v0 = du_clear'45'frame'45'aux_1324
du_clear'45'frame'45'aux_1324 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1324 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_576 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1326 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.clearBlock
d_clearBlock_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_clearBlock_1328 ~v0 = du_clearBlock_1328
du_clearBlock_1328 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_clearBlock_1328 = coe du_clearBlock_682
-- Once.CCC.Machine.SMCore.ExecFinal._.clearBlock-aux
d_clearBlock'45'aux_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clearBlock'45'aux_1330 ~v0 = du_clearBlock'45'aux_1330
du_clearBlock'45'aux_1330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clearBlock'45'aux_1330 v0 v1 v2 v3
  = coe du_clearBlock'45'aux_678 v2 v3
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1332 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1332 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1334 ~v0 = du_readLoc_1334
du_readLoc_1334 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1334 = coe du_readLoc_526
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1336 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1336 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1338 ~v0 = du_writeHeapMem_1338
du_writeHeapMem_1338 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1338 = coe du_writeHeapMem_664
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1340 ~v0 = du_writeHeapMem'45'aux_1340
du_writeHeapMem'45'aux_1340 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1340 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_658 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1342 v0 = coe d_writeLoc_708 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1344 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1346 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1346 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1348 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1350 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1350 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1352 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1354 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1356 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1356 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1358 ~v0 = du_writeLocToHeap_1358
du_writeLocToHeap_1358 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1358 = coe du_writeLocToHeap_700
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1360 v0 = coe d_writeLocToStack_690 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1362 v0 = coe d_writeStackMem_554 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1364 ~v0 = du_writeStackMem'45'aux_1364
du_writeStackMem'45'aux_1364 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1364 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_546 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1366 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1366 v1 v2
du_exec'45'load'45'with'45'value_1366 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1366 v0 v1
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
d_exec'45'load'45'via'45'resolved_1378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1378 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1378 v1 v2
du_exec'45'load'45'via'45'resolved_1378 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1378 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1366 v0
                  (coe du_readLoc_526 (coe v3) (coe v2)) v3)
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
d_exec'45'store'45'via'45'resolved_1390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1390 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_708 (coe v0) (coe v4) (coe v2) (coe v3))
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
d_exec'45'load'45'suc'45'via'45'resolved_1400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1400 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1400 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1400 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1400 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1366 v0
                  (coe du_readLoc_526 (coe v3) (coe du_sucLoc_78 (coe v2))) v3)
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
d_exec'45'store'45'suc'45'via'45'resolved_1412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1412 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_708
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
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_1422 ~v0 v1 v2 v3
  = du_exec'45'load'45'at'45'resolved_1422 v1 v2 v3
du_exec'45'load'45'at'45'resolved_1422 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_1422 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1366 v1
                  (coe
                     du_readLoc_526 (coe v4) (coe du_offsetLoc_88 (coe v3) (coe v0)))
                  v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v3))
                  (coe d_stackMem_274 (coe v3)) (coe d_heapMem_276 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v3)) (coe d_left_282 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.in-block?
d_in'45'block'63'_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_1438 ~v0 v1 v2 = du_in'45'block'63'_1438 v1 v2
du_in'45'block'63'_1438 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_1438 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe
             ltInt
             (coe
                MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_46 (coe v2))
             (coe
                v0
                (MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                   (coe
                      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-in-block
d_exec'45'store'45'in'45'block_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_1446 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 -> d_writeLoc_708 (coe v0) (coe v4) (coe v2) (coe v3))
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v4))
                  (coe d_stackMem_274 (coe v4)) (coe d_heapMem_276 (coe v4))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v4)) (coe d_left_282 (coe v4))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_1456 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             (\ v5 v6 ->
                coe
                  d_exec'45'store'45'in'45'block_1446 v0
                  (coe
                     du_in'45'block'63'_1438 (coe v1)
                     (coe du_offsetLoc_88 (coe v4) (coe v2)))
                  (coe du_offsetLoc_88 (coe v4) (coe v2)) v5 v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v4 v5 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v5))
                  (coe d_stackMem_274 (coe v5)) (coe d_heapMem_276 (coe v5))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v5)) (coe d_left_282 (coe v5))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-addr-in-block
d_exec'45'addr'45'in'45'block_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_1474 ~v0 v1
  = du_exec'45'addr'45'in'45'block_1474 v1
du_exec'45'addr'45'in'45'block_1474 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_1474 v0
  = if coe v0
      then coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_286
                  (coe
                     du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                     (coe C_SV'45'Ptr_66 (coe v1)))
                  (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                  (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                  (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
      else coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v2))
                  (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v2)) (coe d_left_282 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
-- Once.CCC.Machine.SMCore.ExecFinal.exec-addr-at-resolved
d_exec'45'addr'45'at'45'resolved_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_1482 ~v0 v1 v2 v3
  = du_exec'45'addr'45'at'45'resolved_1482 v1 v2 v3
du_exec'45'addr'45'at'45'resolved_1482 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_1482 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'addr'45'in'45'block_1474
                  (coe
                     du_in'45'block'63'_1438 (coe v0)
                     (coe du_offsetLoc_88 (coe v3) (coe v1)))
                  (coe du_offsetLoc_88 (coe v3) (coe v1)) v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v3))
                  (coe d_stackMem_274 (coe v3)) (coe d_heapMem_276 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v3)) (coe d_left_282 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.live-frames
d_live'45'frames_1498 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_1498 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_450 (coe v0))
         (coe d_frame'45'slots_454 (coe v0)))
      (coe d_saved'45'frames_452 (coe v0))
-- Once.CCC.Machine.SMCore.ExecFinal.in-window
d_in'45'window_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_1502 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_win'45'pick_1306
                    (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v6 v2)
                    (coe ltInt (coe v3) (coe v7))
                    (coe d_in'45'window_1502 (coe v0) (coe v5) (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.stack-gate
d_stack'45'gate_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_1518 ~v0 v1 v2 = du_stack'45'gate_1518 v1 v2
du_stack'45'gate_1518 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_1518 v0 v1
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Machine.SMCore.ExecFinal.live-size
d_live'45'size_1522 :: T_AllocState_348 -> Integer -> Integer
d_live'45'size_1522 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_freed_462 v0 v1) (coe (0 :: Integer))
      (coe d_block'45'size_460 v0 v1)
-- Once.CCC.Machine.SMCore.ExecFinal.rec-at
d_rec'45'at_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'at_1528 ~v0 v1 v2 = du_rec'45'at_1528 v1 v2
du_rec'45'at_1528 ::
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'at_1528 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_48
                   (coe
                      MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
                      (coe (0 :: Integer)))
                   (coe v1)))
-- Once.CCC.Machine.SMCore.ExecFinal.rec-gate
d_rec'45'gate_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'gate_1532 ~v0 v1 v2 = du_rec'45'gate_1532 v1 v2
du_rec'45'gate_1532 ::
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'gate_1532 v0 v1
  = coe
      du_rec'45'at_1528 (coe d_next'45'heap'45'ref_458 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.ExecFinal.frame-gate
d_frame'45'gate_1538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_1538 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe
                    du_stack'45'gate_1518
                    (coe
                       d_in'45'window_1502 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe d_current'45'frame_450 (coe v1))
                             (coe d_frame'45'slots_454 (coe v1)))
                          (coe d_saved'45'frames_452 (coe v1)))
                       (coe v5) (coe addInt (coe v2) (coe v6)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.heap-gate
d_heap'45'gate_1558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_1558 ~v0 v1 = du_heap'45'gate_1558 v1
du_heap'45'gate_1558 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_1558 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2 -> coe v0
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.stack-gate-or
d_stack'45'gate'45'or_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_1566 ~v0 v1 ~v2
  = du_stack'45'gate'45'or_1566 v1
du_stack'45'gate'45'or_1566 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_1566 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Once.CCC.Machine.SMCore.ExecFinal.stack-gate-true
d_stack'45'gate'45'true_1576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_1576 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.gate-or
d_gate'45'or_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_1588 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_stack'45'gate'45'or_1566
             (coe
                d_in'45'window_1502 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe d_current'45'frame_450 (coe v1))
                      (coe d_frame'45'slots_454 (coe v1)))
                   (coe d_saved'45'frames_452 (coe v1)))
                (coe v4) (coe addInt (coe v2) (coe v5)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.range-ok
d_range'45'ok_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_1604 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                C_SV'45'Ptr_66 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
                         -> coe
                              d_in'45'window_1502 (coe v0) (coe v1) (coe v6)
                              (coe addInt (coe v4) (coe v7))
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_SV'45'Tag_68 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Lit_72 v5 v6 v7
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Code_74 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecFinal.ans-ok
d_ans'45'ok_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_ans'45'ok_1632 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                C_SV'45'Ptr_66 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
                         -> coe
                              d_in'45'window_1502 (coe v0) (coe v1) (coe v6)
                              (coe addInt (coe v4) (coe v7))
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_SV'45'Tag_68 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Lit_72 v5 v6 v7
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Code_74 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1294 -> T_LocState_254 -> T_LocState_254
d_exec_1660 v0 v1
  = case coe v1 of
      C_load_1298 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1378 v2
                  (coe du_resolveSourceExt_1264 (coe d_regs_272 (coe v4)) (coe v3))
                  v4)
      C_store_1300 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1390 v0
                  (coe du_resolveSourceExt_1264 (coe d_regs_272 (coe v4)) (coe v2))
                  (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe v3)) v4)
      C_mov_1302 v2 v3
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
d_exec'45'load'45'just_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1686 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1692 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1294] -> T_LocState_254 -> T_LocState_254
d_execList_1694 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1694 (coe v0) (coe v4) (coe d_exec_1660 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1726 v0 = coe d_clear'45'frame_582 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1728 ~v0 = du_clear'45'frame'45'aux_1728
du_clear'45'frame'45'aux_1728 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1728 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_576 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1730 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.clearBlock
d_clearBlock_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_clearBlock_1732 ~v0 = du_clearBlock_1732
du_clearBlock_1732 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_clearBlock_1732 = coe du_clearBlock_682
-- Once.CCC.Machine.SMCore.ExecLemmas._.clearBlock-aux
d_clearBlock'45'aux_1734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clearBlock'45'aux_1734 ~v0 = du_clearBlock'45'aux_1734
du_clearBlock'45'aux_1734 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clearBlock'45'aux_1734 v0 v1 v2 v3
  = coe du_clearBlock'45'aux_678 v2 v3
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1736 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1736 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1738 ~v0 = du_readLoc_1738
du_readLoc_1738 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1738 = coe du_readLoc_526
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1740 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1740 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1742 ~v0 = du_writeHeapMem_1742
du_writeHeapMem_1742 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1742 = coe du_writeHeapMem_664
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1744 ~v0 = du_writeHeapMem'45'aux_1744
du_writeHeapMem'45'aux_1744 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1744 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_658 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1746 v0 = coe d_writeLoc_708 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1748 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1750 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1750 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1752 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1754 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1754 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1756 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1758 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1760 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1760 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1762 ~v0 = du_writeLocToHeap_1762
du_writeLocToHeap_1762 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1762 = coe du_writeLocToHeap_700
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1764 v0 = coe d_writeLocToStack_690 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1766 v0 = coe d_writeStackMem_554 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1768 ~v0 = du_writeStackMem'45'aux_1768
du_writeStackMem'45'aux_1768 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1768 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_546 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.ans-ok
d_ans'45'ok_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_ans'45'ok_1772 v0 = coe d_ans'45'ok_1632 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1294 -> T_LocState_254 -> T_LocState_254
d_exec_1774 v0 = coe d_exec_1660 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-addr-at-resolved
d_exec'45'addr'45'at'45'resolved_1776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_1776 ~v0
  = du_exec'45'addr'45'at'45'resolved_1776
du_exec'45'addr'45'at'45'resolved_1776 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_1776
  = coe du_exec'45'addr'45'at'45'resolved_1482
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-addr-in-block
d_exec'45'addr'45'in'45'block_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_1778 ~v0
  = du_exec'45'addr'45'in'45'block_1778
du_exec'45'addr'45'in'45'block_1778 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_1778
  = coe du_exec'45'addr'45'in'45'block_1474
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_1780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_1780 ~v0
  = du_exec'45'load'45'at'45'resolved_1780
du_exec'45'load'45'at'45'resolved_1780 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_1780
  = coe du_exec'45'load'45'at'45'resolved_1422
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1782 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1784 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1786 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1786
du_exec'45'load'45'suc'45'via'45'resolved_1786 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1786
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1400
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1788 ~v0
  = du_exec'45'load'45'via'45'resolved_1788
du_exec'45'load'45'via'45'resolved_1788 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1788
  = coe du_exec'45'load'45'via'45'resolved_1378
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1790 ~v0
  = du_exec'45'load'45'with'45'value_1790
du_exec'45'load'45'with'45'value_1790 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1790
  = coe du_exec'45'load'45'with'45'value_1366
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_1792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_1792 v0
  = coe d_exec'45'store'45'at'45'resolved_1456 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-in-block
d_exec'45'store'45'in'45'block_1794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_1794 v0
  = coe d_exec'45'store'45'in'45'block_1446 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1796 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1412 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1798 v0
  = coe d_exec'45'store'45'via'45'resolved_1390 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1294] -> T_LocState_254 -> T_LocState_254
d_execList_1800 v0 = coe d_execList_1694 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.frame-gate
d_frame'45'gate_1802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_1802 v0 = coe d_frame'45'gate_1538 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.gate-or
d_gate'45'or_1804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_1804 v0 = coe d_gate'45'or_1588 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.heap-gate
d_heap'45'gate_1806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_1806 ~v0 = du_heap'45'gate_1806
du_heap'45'gate_1806 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_1806 = coe du_heap'45'gate_1558
-- Once.CCC.Machine.SMCore.ExecLemmas._.in-block?
d_in'45'block'63'_1808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_1808 ~v0 = du_in'45'block'63'_1808
du_in'45'block'63'_1808 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_1808 = coe du_in'45'block'63'_1438
-- Once.CCC.Machine.SMCore.ExecLemmas._.in-window
d_in'45'window_1810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_1810 v0 = coe d_in'45'window_1502 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.live-frames
d_live'45'frames_1812 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_1812 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_450 (coe v0))
         (coe d_frame'45'slots_454 (coe v0)))
      (coe d_saved'45'frames_452 (coe v0))
-- Once.CCC.Machine.SMCore.ExecLemmas._.live-size
d_live'45'size_1814 :: T_AllocState_348 -> Integer -> Integer
d_live'45'size_1814 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_freed_462 v0 v1) (coe (0 :: Integer))
      (coe d_block'45'size_460 v0 v1)
-- Once.CCC.Machine.SMCore.ExecLemmas._.range-ok
d_range'45'ok_1816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_1816 v0 = coe d_range'45'ok_1604 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.rec-at
d_rec'45'at_1818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'at_1818 ~v0 = du_rec'45'at_1818
du_rec'45'at_1818 ::
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'at_1818 = coe du_rec'45'at_1528
-- Once.CCC.Machine.SMCore.ExecLemmas._.rec-gate
d_rec'45'gate_1820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'gate_1820 ~v0 = du_rec'45'gate_1820
du_rec'45'gate_1820 ::
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'gate_1820 = coe du_rec'45'gate_1532
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate
d_stack'45'gate_1822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_1822 ~v0 = du_stack'45'gate_1822
du_stack'45'gate_1822 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_1822 = coe du_stack'45'gate_1518
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate-or
d_stack'45'gate'45'or_1824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_1824 ~v0 = du_stack'45'gate'45'or_1824
du_stack'45'gate'45'or_1824 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_1824 v0 v1
  = coe du_stack'45'gate'45'or_1566 v0
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate-true
d_stack'45'gate'45'true_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_1826 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_LocSourceExt_1246 -> Maybe T_StoredValue_62
d_resolved'45'readLoc_1828 ~v0 v1 v2
  = du_resolved'45'readLoc_1828 v1 v2
du_resolved'45'readLoc_1828 ::
  T_LocState_254 -> T_LocSourceExt_1246 -> Maybe T_StoredValue_62
du_resolved'45'readLoc_1828 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1264 (coe d_regs_272 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_526 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1858 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1928 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2004 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2034 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2090 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2142 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2194 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2210 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2228 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2242 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2260 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1246 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2326 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2350 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2378 = ()
data T_FlatCtrl_2378
  = C_c'45'label_2380 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2382 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2384 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'entry_2386 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                      Integer |
    C_c'45'ret_2388 Integer |
    C_c'45'call'45'fn_2390 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_c'45'start_2392 Integer | C_c'45'leave_2394
-- Once.CCC.Machine.SMCore.rec-size
d_rec'45'size_2402 :: Integer
d_rec'45'size_2402 = coe (64 :: Integer)
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2404 = ()
data T_AbstractInstr_2404
  = C_mov'45'to'45'output_2406 | C_mov'45'to'45'input_2408 |
    C_load'45'indirect_2410 | C_load'45'indirect'45'suc_2412 |
    C_load'45'from'45'slot_2414 Integer |
    C_store'45'at'45'slot_2416 Integer | C_store'45'indirect_2418 |
    C_store'45'indirect'45'suc_2420 | C_lea'45'slot_2422 Integer |
    C_restore'45'input_2424 Integer |
    C_instr'45'alloc'45'stack_2426 Integer |
    C_instr'45'dealloc'45'stack_2428 Integer |
    C_instr'45'reclaim'45'to_2430 Integer |
    C_instr'45'push'45'frame_2432 Integer |
    C_instr'45'pop'45'frame_2434 | C_instr'45'call'45'closure_2436 |
    C_worklist'45'init_2438 Integer | C_worklist'45'push_2440 Integer |
    C_worklist'45'pop_2442 Integer | C_worklist'45'check_2444 Integer |
    C_instr'45'sigop_2450 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 |
    C_instr'45'load'45'const_2456 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                  MAlonzo.Code.Once.Type.T_FitsInReg_24 AgdaAny |
    C_instr'45'load'45'code'45'addr_2458 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2460 |
    C_instr'45'load'45'tag'45'lit_2462 Integer |
    C_instr'45'alloc'45'heap_2464 Integer | C_instr'45'reg'45'op_2466 |
    C_instr'45'ctrl_2468 T_FlatCtrl_2378 |
    C_instr'45'free'45'heap_2470 Integer |
    C_instr'45'room_2472 Integer | C_load'45'at_2474 Integer |
    C_store'45'at_2476 Integer | C_addr'45'at_2478 Integer |
    C_load'45'rec_2480 Integer | C_store'45'rec_2482 Integer
-- Once.CCC.Machine.SMCore.CallI
d_CallI_2484 :: T_AbstractInstr_2404 -> ()
d_CallI_2484 = erased
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2486 :: ()
d_AbstractTrace_2486 = erased
-- Once.CCC.Machine.SMCore.CompUnit
d_CompUnit_2488 = ()
data T_CompUnit_2488
  = C_unit_2502 Integer [T_AbstractInstr_2404]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Machine.SMCore.CompUnit.entry-budget
d_entry'45'budget_2496 :: T_CompUnit_2488 -> Integer
d_entry'45'budget_2496 v0
  = case coe v0 of
      C_unit_2502 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.entry
d_entry_2498 :: T_CompUnit_2488 -> [T_AbstractInstr_2404]
d_entry_2498 v0
  = case coe v0 of
      C_unit_2502 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.blocks
d_blocks_2500 ::
  T_CompUnit_2488 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2500 v0
  = case coe v0 of
      C_unit_2502 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.block-layout
d_block'45'layout_2504 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_AbstractInstr_2404]
d_block'45'layout_2504 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_instr'45'ctrl_2468
                       (coe
                          C_c'45'entry_2386
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_instr'45'ctrl_2468 (coe C_c'45'ret_2388 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout
d_blocks'45'layout_2512 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_AbstractInstr_2404]
d_blocks'45'layout_2512 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_block'45'layout_2504 (coe v1))
             (coe d_blocks'45'layout_2512 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout-++
d_blocks'45'layout'45''43''43'_2522 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blocks'45'layout'45''43''43'_2522 = erased
-- Once.CCC.Machine.SMCore.link
d_link_2534 :: T_CompUnit_2488 -> [T_AbstractInstr_2404]
d_link_2534 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2498 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2468
            (coe C_c'45'ret_2388 (coe d_entry'45'budget_2496 (coe v0))))
         (coe d_blocks'45'layout_2512 (coe d_blocks_2500 (coe v0))))
-- Once.CCC.Machine.SMCore.link-top
d_link'45'top_2538 :: T_CompUnit_2488 -> [T_AbstractInstr_2404]
d_link'45'top_2538 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2498 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe C_instr'45'ctrl_2468 (coe C_c'45'leave_2394))
         (coe d_blocks'45'layout_2512 (coe d_blocks_2500 (coe v0))))
-- Once.CCC.Machine.SMCore.link-pre
d_link'45'pre_2542 ::
  T_CompUnit_2488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> [T_AbstractInstr_2404]
d_link'45'pre_2542 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2498 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2468
            (coe C_c'45'ret_2388 (coe d_entry'45'budget_2496 (coe v0))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_blocks'45'layout_2512 (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  C_instr'45'ctrl_2468
                  (coe
                     C_c'45'entry_2386
                     (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
                     (coe v3)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMCore.link-post
d_link'45'post_2552 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [T_AbstractInstr_2404]
d_link'45'post_2552 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_instr'45'ctrl_2468 (coe C_c'45'ret_2388 (coe v1)))
      (coe d_blocks'45'layout_2512 (coe v0))
-- Once.CCC.Machine.SMCore.link-block-split
d_link'45'block'45'split_2570 ::
  T_CompUnit_2488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2404] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_link'45'block'45'split_2570 = erased
-- Once.CCC.Machine.SMCore._.inner
d_inner_2590 ::
  T_CompUnit_2488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2404] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_2590 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2598 = ()
data T_TreeTrace_2598
  = C_ε_2600 | C_instr_2602 T_AbstractInstr_2404 |
    C__'9656'__2604 T_TreeTrace_2598 T_TreeTrace_2598 |
    C_branch_2606 Integer T_TreeTrace_2598 T_TreeTrace_2598 |
    C_call'45'sub_2608 T_TreeTrace_2598 |
    C_flat_2610 [T_AbstractInstr_2404]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2612 :: [T_AbstractInstr_2404] -> T_TreeTrace_2598
d_flatToTree_2612 v0
  = case coe v0 of
      [] -> coe C_ε_2600
      (:) v1 v2
        -> coe
             C__'9656'__2604 (coe C_instr_2602 (coe v1))
             (coe d_flatToTree_2612 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2618 :: T_TreeTrace_2598 -> [T_AbstractInstr_2404]
d_treeToFlat_2618 v0
  = case coe v0 of
      C_ε_2600 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2602 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2604 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2618 (coe v1)) (coe d_treeToFlat_2618 (coe v2))
      C_branch_2606 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2618 (coe v2)) (coe d_treeToFlat_2618 (coe v3))
      C_call'45'sub_2608 v1 -> coe d_treeToFlat_2618 (coe v1)
      C_flat_2610 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2634 ::
  Integer -> T_TreeTrace_2598 -> [T_AbstractInstr_2404]
d_treeToRunnable_2634 v0 v1
  = case coe v1 of
      C_ε_2600 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2602 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2604 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2634 (coe v0) (coe v2))
             (coe d_treeToRunnable_2634 (coe v0) (coe v3))
      C_branch_2606 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2634 (coe v0) (coe v3))
             (coe d_treeToRunnable_2634 (coe v0) (coe v4))
      C_call'45'sub_2608 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2440 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2634 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2442 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2610 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2664 ::
  Integer -> T_TreeTrace_2598 -> [T_AbstractInstr_2404]
d_treeToRunnableWithInit_2664 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2438 (coe v0))
      (coe d_treeToRunnable_2634 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.in-memory?
d_in'45'memory'63'_2670 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_in'45'memory'63'_2670 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.in-memory-nofit
d_in'45'memory'45'nofit_2682 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in'45'memory'45'nofit_2682 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_2740 v0 = coe d_clear'45'frame_582 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_2742 ~v0 = du_clear'45'frame'45'aux_2742
du_clear'45'frame'45'aux_2742 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_2742 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_576 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2744 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.clearBlock
d_clearBlock_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_clearBlock_2746 ~v0 = du_clearBlock_2746
du_clearBlock_2746 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_clearBlock_2746 = coe du_clearBlock_682
-- Once.CCC.Machine.SMCore.AbstractExec._.clearBlock-aux
d_clearBlock'45'aux_2748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clearBlock'45'aux_2748 ~v0 = du_clearBlock'45'aux_2748
du_clearBlock'45'aux_2748 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clearBlock'45'aux_2748 v0 v1 v2 v3
  = coe du_clearBlock'45'aux_678 v2 v3
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2750 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_2750 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_2752 ~v0 = du_readLoc_2752
du_readLoc_2752 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_2752 = coe du_readLoc_526
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2754 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_2754 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_2756 ~v0 = du_writeHeapMem_2756
du_writeHeapMem_2756 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_2756 = coe du_writeHeapMem_664
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_2758 ~v0 = du_writeHeapMem'45'aux_2758
du_writeHeapMem'45'aux_2758 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_2758 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_658 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_2760 v0 = coe d_writeLoc_708 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2762 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2764 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2764 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2766 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2768 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2768 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2770 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2772 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2774 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2774 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_2776 ~v0 = du_writeLocToHeap_2776
du_writeLocToHeap_2776 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_2776 = coe du_writeLocToHeap_700
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_2778 v0 = coe d_writeLocToStack_690 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_2780 v0 = coe d_writeStackMem_554 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_2782 ~v0 = du_writeStackMem'45'aux_2782
du_writeStackMem'45'aux_2782 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_2782 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_546 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.ans-ok
d_ans'45'ok_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_ans'45'ok_2786 v0 = coe d_ans'45'ok_1632 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1294 -> T_LocState_254 -> T_LocState_254
d_exec_2788 v0 = coe d_exec_1660 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-addr-at-resolved
d_exec'45'addr'45'at'45'resolved_2790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_2790 ~v0
  = du_exec'45'addr'45'at'45'resolved_2790
du_exec'45'addr'45'at'45'resolved_2790 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_2790
  = coe du_exec'45'addr'45'at'45'resolved_1482
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-addr-in-block
d_exec'45'addr'45'in'45'block_2792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_2792 ~v0
  = du_exec'45'addr'45'in'45'block_2792
du_exec'45'addr'45'in'45'block_2792 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_2792
  = coe du_exec'45'addr'45'in'45'block_1474
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_2794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_2794 ~v0
  = du_exec'45'load'45'at'45'resolved_2794
du_exec'45'load'45'at'45'resolved_2794 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_2794
  = coe du_exec'45'load'45'at'45'resolved_1422
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2796 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2798 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_2800 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2800
du_exec'45'load'45'suc'45'via'45'resolved_2800 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_2800
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1400
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_2802 ~v0
  = du_exec'45'load'45'via'45'resolved_2802
du_exec'45'load'45'via'45'resolved_2802 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_2802
  = coe du_exec'45'load'45'via'45'resolved_1378
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_2804 ~v0
  = du_exec'45'load'45'with'45'value_2804
du_exec'45'load'45'with'45'value_2804 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_2804
  = coe du_exec'45'load'45'with'45'value_1366
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_2806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_2806 v0
  = coe d_exec'45'store'45'at'45'resolved_1456 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-in-block
d_exec'45'store'45'in'45'block_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_2808 v0
  = coe d_exec'45'store'45'in'45'block_1446 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_2810 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1412 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_2812 v0
  = coe d_exec'45'store'45'via'45'resolved_1390 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1294] -> T_LocState_254 -> T_LocState_254
d_execList_2814 v0 = coe d_execList_1694 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.frame-gate
d_frame'45'gate_2816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_2816 v0 = coe d_frame'45'gate_1538 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.gate-or
d_gate'45'or_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_2818 v0 = coe d_gate'45'or_1588 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.heap-gate
d_heap'45'gate_2820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_2820 ~v0 = du_heap'45'gate_2820
du_heap'45'gate_2820 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_2820 = coe du_heap'45'gate_1558
-- Once.CCC.Machine.SMCore.AbstractExec._.in-block?
d_in'45'block'63'_2822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_2822 ~v0 = du_in'45'block'63'_2822
du_in'45'block'63'_2822 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_2822 = coe du_in'45'block'63'_1438
-- Once.CCC.Machine.SMCore.AbstractExec._.in-window
d_in'45'window_2824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_2824 v0 = coe d_in'45'window_1502 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.live-frames
d_live'45'frames_2826 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_2826 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_450 (coe v0))
         (coe d_frame'45'slots_454 (coe v0)))
      (coe d_saved'45'frames_452 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec._.live-size
d_live'45'size_2828 :: T_AllocState_348 -> Integer -> Integer
d_live'45'size_2828 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_freed_462 v0 v1) (coe (0 :: Integer))
      (coe d_block'45'size_460 v0 v1)
-- Once.CCC.Machine.SMCore.AbstractExec._.range-ok
d_range'45'ok_2830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_2830 v0 = coe d_range'45'ok_1604 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.rec-at
d_rec'45'at_2832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'at_2832 ~v0 = du_rec'45'at_2832
du_rec'45'at_2832 ::
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'at_2832 = coe du_rec'45'at_1528
-- Once.CCC.Machine.SMCore.AbstractExec._.rec-gate
d_rec'45'gate_2834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_rec'45'gate_2834 ~v0 = du_rec'45'gate_2834
du_rec'45'gate_2834 ::
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_rec'45'gate_2834 = coe du_rec'45'gate_1532
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate
d_stack'45'gate_2836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_2836 ~v0 = du_stack'45'gate_2836
du_stack'45'gate_2836 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_2836 = coe du_stack'45'gate_1518
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate-or
d_stack'45'gate'45'or_2838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_2838 ~v0 = du_stack'45'gate'45'or_2838
du_stack'45'gate'45'or_2838 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_2838 v0 v1
  = coe du_stack'45'gate'45'or_1566 v0
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate-true
d_stack'45'gate'45'true_2840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_2840 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2842 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2842 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2842 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2842 v0 v1 v2
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
d_exec'45'restore'45'input'45'with'45'value_2854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2854 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2854 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2854 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2854 v0 v1 v2
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
d_exec'45'load'45'from'45'slot'45'just_2872 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2872 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2878 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2878 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2886 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2886 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2892 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2892 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62
d_unit'45'storedvalue_2894 ~v0 = du_unit'45'storedvalue_2894
du_unit'45'storedvalue_2894 :: T_StoredValue_62
du_unit'45'storedvalue_2894
  = coe
      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2900 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2900 v3 v4
du_combine'45'typed_2900 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2900 v0 v1
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
d_readTyped'45'int_2906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'int_2906 ~v0 v1 = du_readTyped'45'int_2906 v1
du_readTyped'45'int_2906 :: Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'int_2906 v0
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
d_readTyped'45'float_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'float_2910 ~v0 v1 = du_readTyped'45'float_2910 v1
du_readTyped'45'float_2910 ::
  Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'float_2910 v0
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
d_readTyped'45'cell_2916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
d_readTyped'45'cell_2916 ~v0 ~v1 v2 v3 v4
  = du_readTyped'45'cell_2916 v2 v3 v4
du_readTyped'45'cell_2916 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
du_readTyped'45'cell_2916 v0 v1 v2
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
d_readTyped'45'pair_2952 ::
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
d_readTyped'45'pair_2952 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_readTyped'45'pair_2952 v3 v4 v5 v6 v7 v8
du_readTyped'45'pair_2952 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2952 v0 v1 v2 v3 v4 v5
  = coe
      du_combine'45'typed_2900
      (coe du_readTyped'45'cell_2916 (coe v0) (coe v2) (coe v4))
      (coe du_readTyped'45'cell_2916 (coe v1) (coe v3) (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
d_readReg'45'typed_2968 ~v0 v1 v2 = du_readReg'45'typed_2968 v1 v2
du_readReg'45'typed_2968 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
du_readReg'45'typed_2968 v0 v1
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
d_readTyped'45'sum_2978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_2978 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'sum_2978 v3 v4 v5 v6
du_readTyped'45'sum_2978 ::
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_2978 v0 v1 v2 v3
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
-- Once.CCC.Machine.SMCore.AbstractExec.tsize
d_tsize_3022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_tsize_3022 ~v0 v1 = du_tsize_3022 v1
du_tsize_3022 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_tsize_3022 v0
  = let v1 = 1 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe (0 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe (0 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe
                addInt (coe du_tsize_3022 (coe v2)) (coe du_tsize_3022 (coe v3))
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
           -> coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe du_tsize_3022 (coe v2)) (coe du_tsize_3022 (coe v3)))
         MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (1 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (1 :: Integer)
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_3034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
d_readTyped_3034 ~v0 v1 v2 v3 = du_readTyped_3034 v1 v2 v3
du_readTyped_3034 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
du_readTyped_3034 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
           -> coe
                du_combine'45'typed_2900
                (coe du_readTyped_3034 (coe v4) (coe v1) (coe v2))
                (coe
                   du_readTyped_3034 (coe v5)
                   (coe du_offsetLoc_88 (coe v1) (coe du_tsize_3022 (coe v4)))
                   (coe v2))
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
           -> coe
                du_readTyped'45'sum_2978
                (coe
                   (\ v6 ->
                      coe
                        du_readTyped_3034 (coe v4) (coe du_sucLoc_78 (coe v1)) (coe v2)))
                (coe
                   (\ v6 ->
                      coe
                        du_readTyped_3034 (coe v5) (coe du_sucLoc_78 (coe v1)) (coe v2)))
                (coe du_readLoc_526 (coe v2) (coe v1))
                (coe du_readLoc_526 (coe v2) (coe du_sucLoc_78 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> coe
                du_readTyped'45'int_2906 (coe du_readLoc_526 (coe v2) (coe v1))
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> coe
                du_readTyped'45'float_2910 (coe du_readLoc_526 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.zero-word
d_zero'45'word_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62
d_zero'45'word_3072 ~v0 = du_zero'45'word_3072
du_zero'45'word_3072 :: T_StoredValue_62
du_zero'45'word_3072
  = coe
      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.writeZeros
d_writeZeros_3074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_writeZeros_3074 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_writeZeros_3074 (coe v0) (coe v4) (coe du_sucLoc_78 (coe v2))
                (coe
                   d_writeLoc_708 (coe v0) (coe v3) (coe v2)
                   (coe du_zero'45'word_3072)))
-- Once.CCC.Machine.SMCore.AbstractExec.writeTyped
d_writeTyped_3088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_writeTyped_3088 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v4
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d_writeTyped_3088 (coe v0) (coe v6) (coe v8)
                    (coe du_offsetLoc_88 (coe v3) (coe du_tsize_3022 (coe v5)))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v5) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    d_writeZeros_3074 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_3022 (coe v5)) (coe du_tsize_3022 (coe v6)))
                       (coe du_tsize_3022 (coe v5)))
                    (coe
                       du_offsetLoc_88 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_3022 (coe v5))))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v5) (coe v7)
                       (coe du_sucLoc_78 (coe v3))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v4) (coe v3)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer)))))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    d_writeZeros_3074 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_3022 (coe v5)) (coe du_tsize_3022 (coe v6)))
                       (coe du_tsize_3022 (coe v6)))
                    (coe
                       du_offsetLoc_88 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_3022 (coe v6))))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v6) (coe v7)
                       (coe du_sucLoc_78 (coe v3))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v4) (coe v3)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             d_writeLoc_708 (coe v0) (coe v4) (coe v3)
             (coe
                C_SV'45'Lit_72 (coe v1)
                (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             d_writeLoc_708 (coe v0) (coe v4) (coe v3)
             (coe
                C_SV'45'Lit_72 (coe v1)
                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v2))
      _ -> coe v4
-- Once.CCC.Machine.SMCore.AbstractExec.PlainWord
d_PlainWord_3142 a0 a1 = ()
data T_PlainWord_3142 = C_pw'45'lit_3150 | C_pw'45'tag_3154
-- Once.CCC.Machine.SMCore.AbstractExec.zeros-keeps
d_zeros'45'keeps_3170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_zeros'45'keeps_3170 v0 ~v1 v2 v3 v4 v5 v6
  = du_zeros'45'keeps_3170 v0 v2 v3 v4 v5 v6
du_zeros'45'keeps_3170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_zeros'45'keeps_3170 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      0 -> coe v5
      _ -> let v6 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                du_zeros'45'keeps_3170 (coe v0) (coe v1) (coe v6)
                (coe du_sucLoc_78 (coe v3))
                (coe
                   d_writeLoc_708 (coe v0) (coe v4) (coe v3)
                   (coe
                      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26)
                      (coe (0 :: Integer))))
                (coe
                   v1 v4 v3
                   (coe
                      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer)))
                   (coe C_pw'45'lit_3150) v5))
-- Once.CCC.Machine.SMCore.AbstractExec.writeTyped-keeps
d_writeTyped'45'keeps_3210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_writeTyped'45'keeps_3210 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_writeTyped'45'keeps_3210 v0 v2 v3 v4 v5 v6 v7
du_writeTyped'45'keeps_3210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_writeTyped'45'keeps_3210 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v7 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_writeTyped'45'keeps_3210 (coe v0) (coe v1) (coe v8) (coe v10)
                    (coe du_offsetLoc_88 (coe v4) (coe du_tsize_3022 (coe v7)))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v7) (coe v9) (coe v4) (coe v5))
                    (coe
                       du_writeTyped'45'keeps_3210 (coe v0) (coe v1) (coe v7) (coe v9)
                       (coe v4) (coe v5) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> coe
                    du_zeros'45'keeps_3170 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_3022 (coe v7)) (coe du_tsize_3022 (coe v8)))
                       (coe du_tsize_3022 (coe v7)))
                    (coe
                       du_offsetLoc_88 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_3022 (coe v7))))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v7) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer)))))
                    (coe
                       du_writeTyped'45'keeps_3210 (coe v0) (coe v1) (coe v7) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer))))
                       (coe
                          v1 v5 v4 (coe C_SV'45'Tag_68 (coe (0 :: Integer)))
                          (coe C_pw'45'tag_3154) v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> coe
                    du_zeros'45'keeps_3170 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_3022 (coe v7)) (coe du_tsize_3022 (coe v8)))
                       (coe du_tsize_3022 (coe v8)))
                    (coe
                       du_offsetLoc_88 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_3022 (coe v8))))
                    (coe
                       d_writeTyped_3088 (coe v0) (coe v8) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer)))))
                    (coe
                       du_writeTyped'45'keeps_3210 (coe v0) (coe v1) (coe v8) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_708 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer))))
                       (coe
                          v1 v5 v4 (coe C_SV'45'Tag_68 (coe (1 :: Integer)))
                          (coe C_pw'45'tag_3154) v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
        -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v7 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             v1 v5 v4
             (coe
                C_SV'45'Lit_72 (coe v2)
                (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v3))
             (coe C_pw'45'lit_3150) v6
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             v1 v5 v4
             (coe
                C_SV'45'Lit_72 (coe v2)
                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v3))
             (coe C_pw'45'lit_3150) v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_3362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_structured'45'pure'45'sigop'45'output_3362 ~v0 ~v1 ~v2 ~v3 v4
  = du_structured'45'pure'45'sigop'45'output_3362 v4
du_structured'45'pure'45'sigop'45'output_3362 ::
  T_LocState_254 -> T_StoredValue_62
du_structured'45'pure'45'sigop'45'output_3362 v0
  = coe du_readReg_132 (coe d_regs_272 (coe v0)) (coe C_Output_58)
-- Once.CCC.Machine.SMCore.AbstractExec.decode-at
d_decode'45'at_3370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
d_decode'45'at_3370 ~v0 v1 v2 v3 v4
  = du_decode'45'at_3370 v1 v2 v3 v4
du_decode'45'at_3370 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
du_decode'45'at_3370 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
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
         MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v7 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                  -> case coe v2 of
                       C_SV'45'Ptr_66 v11
                         -> coe du_readTyped_3034 (coe v0) (coe v11) (coe v3)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v7 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                  -> case coe v2 of
                       C_SV'45'Ptr_66 v11
                         -> coe du_readTyped_3034 (coe v0) (coe v11) (coe v3)
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.events-at-arg
d_events'45'at'45'arg_3392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_events'45'at'45'arg_3392 ~v0 v1 ~v2 v3 v4
  = du_events'45'at'45'arg_3392 v1 v3 v4
du_events'45'at'45'arg_3392 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_events'45'at'45'arg_3392 v0 v1 v2
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
d_machine'45'events_3406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_machine'45'events_3406 ~v0 v1 ~v2 v3 v4
  = du_machine'45'events_3406 v1 v3 v4
du_machine'45'events_3406 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_machine'45'events_3406 v0 v1 v2
  = coe
      du_events'45'at'45'arg_3392 (coe v0) (coe v1)
      (coe
         du_decode'45'at_3370 (coe v0)
         (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v1))
         (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))
         (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_3418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> T_StoredValue_62
d_call'45'sigop'45'ans'45'at_3418 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             C_SV'45'Lit_72 (coe v2) (coe v5)
             (coe
                MAlonzo.Code.Once.IR.Semantics.Boundary.du_atTarget_62
                (coe
                   MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186 (coe v0))
                (coe v2)
                (coe
                   MAlonzo.Code.Once.IR.Semantics.Trace.d_answer_208
                   (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_134 (coe v0))
                   (d_ev'45'log_280 (coe v4))
                   (coe
                      MAlonzo.Code.Once.IR.Semantics.Trace.C_callOp_76
                      (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3)) (coe v1)
                      (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3)) (coe v2))
                   v6 v8))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2894
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_3448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_StoredValue_62
d_call'45'sigop'45'ans_3448 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           d_call'45'sigop'45'ans'45'at_3418 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v9)
                           (coe
                              du_decode'45'at_3370 (coe v1)
                              (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3))
                              (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56))
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v8) (coe du_unit'45'storedvalue_2894)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_3470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_3470 v0 v1 v2 v3
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
d_call'45'sigop'45'val_3482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 -> T_StoredValue_62
d_call'45'sigop'45'val_3482 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_call'45'sigop'45'ans_3448 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe
                d_call'45'sigop'45'dec_3470 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Output_58)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_3498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_call'45'sigop'45'output_3498 v0 v1 v2 v3 v4
  = coe
      d_call'45'sigop'45'val_3482 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_3510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_pure'45'sigop'45'output_3510 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_3540 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
      (coe
         du_sv'45'as'45'loc_1258
         (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_3516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny -> T_StoredValue_62
d_pure'45'sigop'45'out'45'val_3516 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_res'45'sv_3520 (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_206 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_182 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                   (coe v0))
                v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2894
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.res-sv
d_res'45'sv_3520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
d_res'45'sv_3520 ~v0 v1 v2 v3 = du_res'45'sv_3520 v1 v2 v3
du_res'45'sv_3520 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
du_res'45'sv_3520 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe du_unit'45'storedvalue_2894
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe C_SV'45'Lit_72 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62
d_pure'45'sigop'45'out'45'aux_3540 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    d_pure'45'sigop'45'out'45'val_3516 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe du_readTyped_3034 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    d_pure'45'sigop'45'out'45'val_3516 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2968 (coe v1)
                       (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_structured'45'pure'45'sigop'45'output_3362 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output'45'of_3576 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             d_pure'45'sigop'45'output_3510 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_unit'45'storedvalue_2894
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_unit'45'storedvalue_2894
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             d_call'45'sigop'45'output_3498 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_3590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events'45'of_3590 ~v0 v1 ~v2 v3 v4 v5
  = du_sigop'45'events'45'of_3590 v1 v3 v4 v5
du_sigop'45'events'45'of_3590 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events'45'of_3590 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_machine'45'events_3406 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_machine'45'events_3406 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe du_machine'45'events_3406 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events
d_sigop'45'events_3608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events_3608 ~v0 v1 ~v2 v3 v4
  = du_sigop'45'events_3608 v1 v3 v4
du_sigop'45'events_3608 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events_3608 v0 v1 v2
  = coe
      du_sigop'45'events'45'of_3590 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_3618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output_3618 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_3576 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.unread?
d_unread'63'_3626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Maybe AgdaAny -> Bool
d_unread'63'_3626 ~v0 ~v1 v2 = du_unread'63'_3626 v2
du_unread'63'_3626 :: Maybe AgdaAny -> Bool
du_unread'63'_3626 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-faults-of
d_exec'45'sigop'45'faults'45'of_3632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'faults'45'of_3632 ~v0 v1 ~v2 v3 v4 v5
  = du_exec'45'sigop'45'faults'45'of_3632 v1 v3 v4 v5
du_exec'45'sigop'45'faults'45'of_3632 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'faults'45'of_3632 v0 v1 v2 v3
  = coe
      seq (coe v1)
      (coe
         du_unread'63'_3626
         (coe
            du_decode'45'at_3370 (coe v0)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v2))
            (coe du_readReg_132 (coe d_regs_272 (coe v3)) (coe C_Input1_56))
            (coe v3)))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-faults
d_exec'45'sigop'45'faults_3654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'faults_3654 ~v0 v1 ~v2 v3 v4
  = du_exec'45'sigop'45'faults_3654 v1 v3 v4
du_exec'45'sigop'45'faults_3654 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'faults_3654 v0 v1 v2
  = coe
      du_exec'45'sigop'45'faults'45'of_3632 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts'45'of_3664 ~v0 v1 ~v2 v3 v4 v5
  = du_exec'45'sigop'45'halts'45'of_3664 v1 v3 v4 v5
du_exec'45'sigop'45'halts'45'of_3664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'halts'45'of_3664 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             du_exec'45'sigop'45'faults'45'of_3632 (coe v0) (coe v1) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe
             du_exec'45'sigop'45'faults'45'of_3632 (coe v0)
             (coe MAlonzo.Code.Once.SigOp.Info.C_Emits_64) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             du_exec'45'sigop'45'faults'45'of_3632 (coe v0) (coe v1) (coe v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_3684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts_3684 ~v0 v1 ~v2 v3 v4
  = du_exec'45'sigop'45'halts_3684 v1 v3 v4
du_exec'45'sigop'45'halts_3684 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'halts_3684 v0 v1 v2
  = coe
      du_exec'45'sigop'45'halts'45'of_3664 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.res-just
d_res'45'just_3692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> Maybe AgdaAny
d_res'45'just_3692 ~v0 ~v1 v2 = du_res'45'just_3692 v2
du_res'45'just_3692 ::
  MAlonzo.Code.Once.Res.T_Res_6 -> Maybe AgdaAny
du_res'45'just_3692 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Res.C_returns_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-ans-at
d_call'45'ans'45'at_3702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny -> Maybe AgdaAny
d_call'45'ans'45'at_3702 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     MAlonzo.Code.Once.IR.Semantics.Boundary.du_atTarget_62
                                     (coe
                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                                        (coe v0))
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.IR.Semantics.Trace.d_answer_208
                                        (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_134
                                           (coe v0))
                                        (d_ev'45'log_280 (coe v4))
                                        (coe
                                           MAlonzo.Code.Once.IR.Semantics.Trace.C_callOp_76
                                           (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3))
                                           (coe v1)
                                           (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3))
                                           (coe v2))
                                        v9 v10))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v8) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-ans-at
d_pure'45'ans'45'at_3730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny -> Maybe AgdaAny
d_pure'45'ans'45'at_3730 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_res'45'just_3692
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_206 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_182 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                   (coe v0))
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-answer-of
d_sigop'45'answer'45'of_3742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Maybe AgdaAny
d_sigop'45'answer'45'of_3742 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             d_pure'45'ans'45'at_3730 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                du_decode'45'at_3370 (coe v1)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56))
                (coe v5))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             d_call'45'ans'45'at_3702 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
             (coe
                d_call'45'sigop'45'dec_3470 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe
                du_decode'45'at_3370 (coe v1)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-answer
d_sigop'45'answer_3756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Maybe AgdaAny
d_sigop'45'answer_3756 v0 v1 v2 v3 v4
  = coe
      d_sigop'45'answer'45'of_3742 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-at
d_sigop'45'store'45'at_3764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> T_LocState_254 -> T_LocState_254
d_sigop'45'store'45'at_3764 v0 v1 v2 v3 v4 v5
  = if coe v2
      then case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                      -> coe
                           d_writeTyped_3088 (coe v0) (coe v1) (coe v7) (coe v6) (coe v5)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe v5
-- Once.CCC.Machine.SMCore.AbstractExec.arg-words
d_arg'45'words_3784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
d_arg'45'words_3784 ~v0 v1 v2 = du_arg'45'words_3784 v1 v2
du_arg'45'words_3784 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
du_arg'45'words_3784 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v5 v6
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
                  -> coe du_tsize_3022 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v5 v6
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
                  -> coe du_tsize_3022 (coe v0)
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.ans-words
d_ans'45'words_3790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_ans'45'words_3790 ~v0 v1 = du_ans'45'words_3790 v1
du_ans'45'words_3790 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_ans'45'words_3790 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_in'45'memory'63'_2670 (coe v0)) (coe du_tsize_3022 (coe v0))
      (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-gate
d_sigop'45'gate_3798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_AllocState_348 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_sigop'45'gate_3798 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         d_range'45'ok_1604 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe d_current'45'frame_450 (coe v3))
               (coe d_frame'45'slots_454 (coe v3)))
            (coe d_saved'45'frames_452 (coe v3)))
         (coe
            du_arg'45'words_3784 (coe v1)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4)))
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56)))
      (coe
         d_ans'45'ok_1632 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe d_current'45'frame_450 (coe v3))
               (coe d_frame'45'slots_454 (coe v3)))
            (coe d_saved'45'frames_452 (coe v3)))
         (coe du_ans'45'words_3790 (coe v2))
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Output_58)))
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store
d_sigop'45'store_3814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_LocState_254
d_sigop'45'store_3814 v0 v1 v2 v3 v4
  = coe
      d_sigop'45'store'45'at_3764 (coe v0) (coe v2)
      (coe d_in'45'memory'63'_2670 (coe v2))
      (coe
         du_sv'45'as'45'loc_1258
         (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Output_58)))
      (coe
         d_sigop'45'answer_3756 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-keeps
d_sigop'45'store'45'keeps_3838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_sigop'45'store'45'keeps_3838 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_sigop'45'store'45'keeps_3838 v0 v2 v3 v4 v5 v6 v7
du_sigop'45'store'45'keeps_3838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_sigop'45'store'45'keeps_3838 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_go_3862 (coe v0) (coe v1) (coe v3) (coe v5) (coe v6)
      (coe d_in'45'memory'63'_2670 (coe v3))
      (coe
         du_sv'45'as'45'loc_1258
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Output_58)))
      (coe
         d_sigop'45'answer_3756 (coe v0) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec._.go
d_go_3862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  AgdaAny ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> AgdaAny
d_go_3862 v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10
  = du_go_3862 v0 v2 v4 v6 v7 v8 v9 v10
du_go_3862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3142 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_LocState_254 ->
  AgdaAny ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> AgdaAny
du_go_3862 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v5
      then case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> coe
                           du_writeTyped'45'keeps_3210 (coe v0) (coe v1) (coe v2) (coe v9)
                           (coe v8) (coe v3) (coe v4)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe v4
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-id
d_sigop'45'store'45'id_3878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'store'45'id_3878 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.go
d_go_3894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3894 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.lit-value
d_lit'45'value_3900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
d_lit'45'value_3900 v0 ~v1 v2 v3 = du_lit'45'value_3900 v0 v2 v3
du_lit'45'value_3900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
du_lit'45'value_3900 v0 v1 v2
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
             MAlonzo.Code.Once.Float.Word.d_round_58
             (coe
                MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_132
                (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.heapRefOf
d_heapRefOf_3906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 -> Maybe Integer
d_heapRefOf_3906 ~v0 v1 = du_heapRefOf_3906 v1
du_heapRefOf_3906 :: T_StoredValue_62 -> Maybe Integer
du_heapRefOf_3906 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_SV'45'Ptr_66 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                          (coe
                             MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44 (coe v3)))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.freeAtMem
d_freeAtMem_3910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_freeAtMem_3910 ~v0 v1 v2 = du_freeAtMem_3910 v1 v2
du_freeAtMem_3910 ::
  Maybe Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_freeAtMem_3910 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_clearBlock_682 (coe v1) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.freeAtMark
d_freeAtMark_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> (Integer -> Bool) -> Integer -> Bool
d_freeAtMark_3918 ~v0 v1 v2 v3 = du_freeAtMark_3918 v1 v2 v3
du_freeAtMark_3918 ::
  Maybe Integer -> (Integer -> Bool) -> Integer -> Bool
du_freeAtMark_3918 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe eqInt (coe v2) (coe v3)) (coe v1 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.freeMem
d_freeMem_3930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_freeMem_3930 ~v0 v1 v2 = du_freeMem_3930 v1 v2
du_freeMem_3930 ::
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_freeMem_3930 v0 v1
  = coe du_freeAtMem_3910 (coe du_heapRefOf_3906 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.freeMark
d_freeMark_3936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 -> (Integer -> Bool) -> Integer -> Bool
d_freeMark_3936 ~v0 v1 v2 = du_freeMark_3936 v1 v2
du_freeMark_3936 ::
  T_StoredValue_62 -> (Integer -> Bool) -> Integer -> Bool
du_freeMark_3936 v0 v1
  = coe du_freeAtMark_3918 (coe du_heapRefOf_3906 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.freeMem-keeps
d_freeMem'45'keeps_3950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Maybe T_StoredValue_62 -> ()) ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_freeMem'45'keeps_3950 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du_freeMem'45'keeps_3950 v2 v4 v5 v6
du_freeMem'45'keeps_3950 ::
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_freeMem'45'keeps_3950 v0 v1 v2 v3
  = coe
      du_at_3978 (coe v1) (coe v2) (coe v3)
      (coe du_heapRefOf_3906 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear
d_clear_3974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Maybe T_StoredValue_62 -> ()) ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
d_clear_3974 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9
  = du_clear_3974 v5 v6 v9
du_clear_3974 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_clear_3974 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v0)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec._.at
d_at_3978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Maybe T_StoredValue_62 -> ()) ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny -> AgdaAny -> Maybe Integer -> AgdaAny
d_at_3978 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_at_3978 v4 v5 v6 v7
du_at_3978 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  AgdaAny -> AgdaAny -> Maybe Integer -> AgdaAny
du_at_3978 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_clear_3974 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                   (coe
                      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44 (coe v0)))
                (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.freeMem-just
d_freeMem'45'just_3990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_freeMem'45'just_3990 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.clear-no
d_clear'45'no_4012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'no_4012 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.≡ᵇ-false
d_'8801''7495''45'false_4022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8801''7495''45'false_4022 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.∨-false
d_'8744''45'false_4034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false_4034 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.freeMem-miss
d_freeMem'45'miss_4044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_freeMem'45'miss_4044 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.freeMem-unmarked
d_freeMem'45'unmarked_4064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  (Integer -> Bool) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_freeMem'45'unmarked_4064 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.at
d_at_4082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  (Integer -> Bool) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at_4082 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.freeMark-mono
d_freeMark'45'mono_4094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (Integer -> Bool) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_freeMark'45'mono_4094 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.∨-true
d_'8744''45'true_4112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (Integer -> Bool) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'true_4112 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.at
d_at_4118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  (Integer -> Bool) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at_4118 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.freeBlock
d_freeBlock_4122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freeBlock_4122 ~v0 v1 v2 v3 = du_freeBlock_4122 v1 v2 v3
du_freeBlock_4122 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_freeBlock_4122 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_mkLocState_286 (coe d_regs_272 (coe v1))
         (coe d_stackMem_274 (coe v1))
         (coe du_freeMem_3930 (coe v0) (coe d_heapMem_276 (coe v1)))
         (coe d_halted_278 (coe v1)) (coe d_ev'45'log_280 (coe v1))
         (coe d_left_282 (coe v1)) (coe d_faulted_284 (coe v1)))
      (coe
         C_mkAllocState_464 (coe d_current'45'frame_450 (coe v2))
         (coe d_saved'45'frames_452 (coe v2))
         (coe d_frame'45'slots_454 (coe v2))
         (coe d_next'45'slot_456 (coe v2))
         (coe d_next'45'heap'45'ref_458 (coe v2))
         (coe d_block'45'size_460 (coe v2))
         (coe du_freeMark_3936 (coe v0) (coe d_freed_462 (coe v2))))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_4130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2404 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_4130 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2406
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
      C_mov'45'to'45'input_2408
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
      C_load'45'indirect_2410
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1378 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1258
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2412
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1400 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1258
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2414 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2842
             (coe
                du_readLoc_526 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_450 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2416 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_708 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_450 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2418
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1390 v0
                (coe
                   du_sv'45'as'45'loc_1258
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2420
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1412 v0
                (coe
                   du_sv'45'as'45'loc_1258
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2422 v4
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
                         (coe d_current'45'frame_450 (coe v3)) (coe v4))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_restore'45'input_2424 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2854
             (coe
                du_readLoc_526 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_450 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2426 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'dealloc'45'stack_2428 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2430 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'push'45'frame_2432 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2434
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2436
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2438 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2440 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_708 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_450 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2442 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2842
             (coe
                du_readLoc_526 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_450 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2444 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2450 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_3618
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe
                   d_stackMem_274
                   (coe
                      d_sigop'45'store_3814 (coe v0) (coe v4) (coe v5) (coe v6)
                      (coe v2)))
                (coe
                   d_heapMem_276
                   (coe
                      d_sigop'45'store_3814 (coe v0) (coe v4) (coe v5) (coe v6)
                      (coe v2)))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe du_exec'45'sigop'45'halts_3684 (coe v4) (coe v6) (coe v2))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d_not_22
                      (coe
                         d_sigop'45'gate_3798 (coe v0) (coe v4) (coe v5) (coe v3) (coe v6)
                         (coe v2))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_ev'45'log_280 (coe v2))
                   (coe du_sigop'45'events_3608 (coe v4) (coe v6) (coe v2)))
                (coe d_left_282 (coe v2))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe du_exec'45'sigop'45'faults_3654 (coe v4) (coe v6) (coe v2))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d_not_22
                         (coe
                            d_sigop'45'gate_3798 (coe v0) (coe v4) (coe v5) (coe v3) (coe v6)
                            (coe v2)))
                      (coe d_faulted_284 (coe v2)))))
             (coe v3)
      C_instr'45'load'45'const_2456 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_72 (coe v4) (coe v5)
                      (coe du_lit'45'value_3900 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2458 v4
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
      C_instr'45'save'45'closure'45'reg_2460
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2462 v4
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
      C_instr'45'alloc'45'heap_2464 v4
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
                               (coe d_next'45'heap'45'ref_458 (coe v3)))))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe
                C_mkAllocState_464 (coe d_current'45'frame_450 (coe v3))
                (coe d_saved'45'frames_452 (coe v3))
                (coe d_frame'45'slots_454 (coe v3))
                (coe d_next'45'slot_456 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_458 (coe v3)))))
                (coe
                   d_size'45'with_336 (coe v4)
                   (coe d_next'45'heap'45'ref_458 (coe v3))
                   (coe d_block'45'size_460 (coe v3)))
                (coe d_freed_462 (coe v3)))
      C_instr'45'reg'45'op_2466
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_302 (coe v2)) (coe v3)
      C_instr'45'ctrl_2468 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'free'45'heap_2470 v4
        -> coe
             du_freeBlock_4122
             (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))
             (coe v2) (coe v3)
      C_instr'45'room_2472 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_load'45'at_2474 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'at'45'resolved_1422 v4 (coe C_Output_58)
                (d_frame'45'gate_1538
                   (coe v0) (coe v3) (coe v4)
                   (coe
                      du_sv'45'as'45'loc_1258
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                v2)
             (coe v3)
      C_store'45'at_2476 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'at'45'resolved_1456 v0
                (\ v5 ->
                   coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe d_freed_462 v3 v5) (coe (0 :: Integer))
                     (coe d_block'45'size_460 v3 v5))
                v4
                (d_frame'45'gate_1538
                   (coe v0) (coe v3) (coe v4)
                   (coe
                      du_sv'45'as'45'loc_1258
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_addr'45'at_2478 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'addr'45'at'45'resolved_1482
                (d_block'45'size_460 (coe v3)) v4
                (coe
                   du_heap'45'gate_1558
                   (coe
                      du_sv'45'as'45'loc_1258
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                v2)
             (coe v3)
      C_load'45'rec_2480 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1378 (coe C_Output_58)
                (coe du_rec'45'gate_1532 (coe v3) (coe v4)) v2)
             (coe v3)
      C_store'45'rec_2482 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1390 v0
                (coe du_rec'45'gate_1532 (coe v3) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_4132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2404] ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_4132 v0 v1 v2 v3
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
                       d_exec'45'trace_4132 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_4130 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_4130 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_4380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2404 ->
  [T_AbstractInstr_2404] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_4380 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_4426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2404 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_4426 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_4460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
d_getTag_4460 ~v0 v1 v2 v3 = du_getTag_4460 v1 v2 v3
du_getTag_4460 ::
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
du_getTag_4460 v0 v1 v2
  = let v3
          = coe d_stackMem_274 v0 (d_current'45'frame_450 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_4484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2598 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_4484 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2600
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2602 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_4130 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2604 v4 v5
        -> let v6 = d_halted_278 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_4484 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_4484 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_4484 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2606 v4 v5 v6
        -> let v7 = d_halted_278 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_274 v2 (d_current'45'frame_450 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_4484 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_4484 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_4484 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_4484 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_4484 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2608 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_4484 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2610 v4
        -> coe d_exec'45'trace_4132 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_4644 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_4644 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_4662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2598 ->
  T_TreeTrace_2598 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_4662 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_4708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2404 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_4708 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_4748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2598 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_4748 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_4788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2404] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_4788 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_4802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2598 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_4802 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_4802
du_exec'45'tree'45'flat'45'equiv'45'simple_4802 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_4802
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
