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
-- Once.CCC.Machine.SMCore.win-pick
d_win'45'pick_1286 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> Bool -> Bool
d_win'45'pick_1286 ~v0 v1 v2 v3 = du_win'45'pick_1286 v1 v2 v3
du_win'45'pick_1286 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> Bool -> Bool
du_win'45'pick_1286 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1) (coe v2))
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1302 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1304 ~v0 = du_clear'45'frame'45'aux_1304
du_clear'45'frame'45'aux_1304 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1304 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1306 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1308 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1308 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1310 ~v0 = du_readLoc_1310
du_readLoc_1310 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1310 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1312 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1312 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1314 ~v0 = du_writeHeapMem_1314
du_writeHeapMem_1314 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1314 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1316 ~v0 = du_writeHeapMem'45'aux_1316
du_writeHeapMem'45'aux_1316 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1316 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1318 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1320 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1322 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1322 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1324 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1326 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1326 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1328 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1330 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1332 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1332 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1334 ~v0 = du_writeLocToHeap_1334
du_writeLocToHeap_1334 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1334 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1336 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1338 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1340 ~v0 = du_writeStackMem'45'aux_1340
du_writeStackMem'45'aux_1340 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1340 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1342 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1342 v1 v2
du_exec'45'load'45'with'45'value_1342 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1342 v0 v1
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
d_exec'45'load'45'via'45'resolved_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1354 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1354 v1 v2
du_exec'45'load'45'via'45'resolved_1354 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1354 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1342 v0
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
d_exec'45'store'45'via'45'resolved_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1366 v0 v1
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
d_exec'45'load'45'suc'45'via'45'resolved_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1376 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1376 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1376 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1376 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1342 v0
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
d_exec'45'store'45'suc'45'via'45'resolved_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1388 v0 v1
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
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_1398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_1398 ~v0 v1 v2 v3
  = du_exec'45'load'45'at'45'resolved_1398 v1 v2 v3
du_exec'45'load'45'at'45'resolved_1398 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_1398 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1342 v1
                  (coe
                     du_readLoc_522 (coe v4) (coe du_offsetLoc_88 (coe v3) (coe v0)))
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
d_in'45'block'63'_1414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_1414 ~v0 v1 v2 = du_in'45'block'63'_1414 v1 v2
du_in'45'block'63'_1414 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_1414 v0 v1
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
d_exec'45'store'45'in'45'block_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_1422 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 -> d_writeLoc_688 (coe v0) (coe v4) (coe v2) (coe v3))
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkLocState_286 (coe d_regs_272 (coe v4))
                  (coe d_stackMem_274 (coe v4)) (coe d_heapMem_276 (coe v4))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_280 (coe v4)) (coe d_left_282 (coe v4))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_1432 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             (\ v5 v6 ->
                coe
                  d_exec'45'store'45'in'45'block_1422 v0
                  (coe
                     du_in'45'block'63'_1414 (coe v1)
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
d_exec'45'addr'45'in'45'block_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_1450 ~v0 v1
  = du_exec'45'addr'45'in'45'block_1450 v1
du_exec'45'addr'45'in'45'block_1450 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_1450 v0
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
d_exec'45'addr'45'at'45'resolved_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_1458 ~v0 v1 v2 v3
  = du_exec'45'addr'45'at'45'resolved_1458 v1 v2 v3
du_exec'45'addr'45'at'45'resolved_1458 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_1458 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'addr'45'in'45'block_1450
                  (coe
                     du_in'45'block'63'_1414 (coe v0)
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
d_live'45'frames_1474 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_1474 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_448 (coe v0))
         (coe d_frame'45'slots_452 (coe v0)))
      (coe d_saved'45'frames_450 (coe v0))
-- Once.CCC.Machine.SMCore.ExecFinal.in-window
d_in'45'window_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_1478 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    du_win'45'pick_1286
                    (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__96 v0 v6 v2)
                    (coe ltInt (coe v3) (coe v7))
                    (coe d_in'45'window_1478 (coe v0) (coe v5) (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.stack-gate
d_stack'45'gate_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_1494 ~v0 v1 v2 = du_stack'45'gate_1494 v1 v2
du_stack'45'gate_1494 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_1494 v0 v1
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.CCC.Machine.SMCore.ExecFinal.frame-gate
d_frame'45'gate_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_1498 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe
                    du_stack'45'gate_1494
                    (coe
                       d_in'45'window_1478 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe d_current'45'frame_448 (coe v1))
                             (coe d_frame'45'slots_452 (coe v1)))
                          (coe d_saved'45'frames_450 (coe v1)))
                       (coe v5) (coe addInt (coe v2) (coe v6)))
                    (coe v4)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.heap-gate
d_heap'45'gate_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_1518 ~v0 v1 = du_heap'45'gate_1518 v1
du_heap'45'gate_1518 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_1518 v0
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
d_stack'45'gate'45'or_1526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_1526 ~v0 v1 ~v2
  = du_stack'45'gate'45'or_1526 v1
du_stack'45'gate'45'or_1526 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_1526 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Once.CCC.Machine.SMCore.ExecFinal.stack-gate-true
d_stack'45'gate'45'true_1536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_1536 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.gate-or
d_gate'45'or_1548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_1548 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             du_stack'45'gate'45'or_1526
             (coe
                d_in'45'window_1478 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe d_current'45'frame_448 (coe v1))
                      (coe d_frame'45'slots_452 (coe v1)))
                   (coe d_saved'45'frames_450 (coe v1)))
                (coe v4) (coe addInt (coe v2) (coe v5)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.range-ok
d_range'45'ok_1564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_1564 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                C_SV'45'Ptr_66 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
                         -> coe
                              d_in'45'window_1478 (coe v0) (coe v1) (coe v6)
                              (coe addInt (coe v4) (coe v7))
                       MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_SV'45'Tag_68 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Lit_72 v5 v6 v7
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_SV'45'Code_74 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_1592 v0 v1
  = case coe v1 of
      C_load_1278 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1354 v2
                  (coe du_resolveSourceExt_1244 (coe d_regs_272 (coe v4)) (coe v3))
                  v4)
      C_store_1280 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1366 v0
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
d_exec'45'load'45'just_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1618 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1624 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_1626 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1626 (coe v0) (coe v4) (coe d_exec_1592 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_1658 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_1660 ~v0 = du_clear'45'frame'45'aux_1660
du_clear'45'frame'45'aux_1660 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_1660 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1662 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1664 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_1664 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_1666 ~v0 = du_readLoc_1666
du_readLoc_1666 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_1666 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1668 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_1668 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_1670 ~v0 = du_writeHeapMem_1670
du_writeHeapMem_1670 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_1670 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_1672 ~v0 = du_writeHeapMem'45'aux_1672
du_writeHeapMem'45'aux_1672 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_1672 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_1674 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1676 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1678 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1678 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1680 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1682 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1682 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1684 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1686 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1688 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1688 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_1690 ~v0 = du_writeLocToHeap_1690
du_writeLocToHeap_1690 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_1690 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_1692 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_1694 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_1696 ~v0 = du_writeStackMem'45'aux_1696
du_writeStackMem'45'aux_1696 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_1696 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_1700 v0 = coe d_exec_1592 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-addr-at-resolved
d_exec'45'addr'45'at'45'resolved_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_1702 ~v0
  = du_exec'45'addr'45'at'45'resolved_1702
du_exec'45'addr'45'at'45'resolved_1702 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_1702
  = coe du_exec'45'addr'45'at'45'resolved_1458
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-addr-in-block
d_exec'45'addr'45'in'45'block_1704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_1704 ~v0
  = du_exec'45'addr'45'in'45'block_1704
du_exec'45'addr'45'in'45'block_1704 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_1704
  = coe du_exec'45'addr'45'in'45'block_1450
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_1706 ~v0
  = du_exec'45'load'45'at'45'resolved_1706
du_exec'45'load'45'at'45'resolved_1706 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_1706
  = coe du_exec'45'load'45'at'45'resolved_1398
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1708 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1710 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_1712 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1712
du_exec'45'load'45'suc'45'via'45'resolved_1712 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_1712
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1376
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_1714 ~v0
  = du_exec'45'load'45'via'45'resolved_1714
du_exec'45'load'45'via'45'resolved_1714 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_1714
  = coe du_exec'45'load'45'via'45'resolved_1354
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_1716 ~v0
  = du_exec'45'load'45'with'45'value_1716
du_exec'45'load'45'with'45'value_1716 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_1716
  = coe du_exec'45'load'45'with'45'value_1342
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_1718 v0
  = coe d_exec'45'store'45'at'45'resolved_1432 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-in-block
d_exec'45'store'45'in'45'block_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_1720 v0
  = coe d_exec'45'store'45'in'45'block_1422 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_1722 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1388 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_1724 v0
  = coe d_exec'45'store'45'via'45'resolved_1366 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_1726 v0 = coe d_execList_1626 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.frame-gate
d_frame'45'gate_1728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_1728 v0 = coe d_frame'45'gate_1498 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.gate-or
d_gate'45'or_1730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_1730 v0 = coe d_gate'45'or_1548 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.heap-gate
d_heap'45'gate_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_1732 ~v0 = du_heap'45'gate_1732
du_heap'45'gate_1732 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_1732 = coe du_heap'45'gate_1518
-- Once.CCC.Machine.SMCore.ExecLemmas._.in-block?
d_in'45'block'63'_1734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_1734 ~v0 = du_in'45'block'63'_1734
du_in'45'block'63'_1734 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_1734 = coe du_in'45'block'63'_1414
-- Once.CCC.Machine.SMCore.ExecLemmas._.in-window
d_in'45'window_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_1736 v0 = coe d_in'45'window_1478 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.live-frames
d_live'45'frames_1738 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_1738 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_448 (coe v0))
         (coe d_frame'45'slots_452 (coe v0)))
      (coe d_saved'45'frames_450 (coe v0))
-- Once.CCC.Machine.SMCore.ExecLemmas._.range-ok
d_range'45'ok_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_1740 v0 = coe d_range'45'ok_1564 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate
d_stack'45'gate_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_1742 ~v0 = du_stack'45'gate_1742
du_stack'45'gate_1742 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_1742 = coe du_stack'45'gate_1494
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate-or
d_stack'45'gate'45'or_1744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_1744 ~v0 = du_stack'45'gate'45'or_1744
du_stack'45'gate'45'or_1744 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_1744 v0 v1
  = coe du_stack'45'gate'45'or_1526 v0
-- Once.CCC.Machine.SMCore.ExecLemmas._.stack-gate-true
d_stack'45'gate'45'true_1746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_1746 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_LocSourceExt_1226 -> Maybe T_StoredValue_62
d_resolved'45'readLoc_1748 ~v0 v1 v2
  = du_resolved'45'readLoc_1748 v1 v2
du_resolved'45'readLoc_1748 ::
  T_LocState_254 -> T_LocSourceExt_1226 -> Maybe T_StoredValue_62
du_resolved'45'readLoc_1748 v0 v1
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
d_load'45'result_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1778 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1848 ::
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
d_load'45'preserves'45'reg_1848 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1924 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1954 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2010 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2062 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2114 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2130 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2148 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2162 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1226 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2180 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2246 ::
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
d_load'45'no'45'halt_2246 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2270 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2298 = ()
data T_FlatCtrl_2298
  = C_c'45'label_2300 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2302 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2304 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'entry_2306 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                      Integer |
    C_c'45'ret_2308 Integer |
    C_c'45'call'45'fn_2310 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_c'45'start_2312 Integer | C_c'45'leave_2314
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2322 = ()
data T_AbstractInstr_2322
  = C_mov'45'to'45'output_2324 | C_mov'45'to'45'input_2326 |
    C_load'45'indirect_2328 | C_load'45'indirect'45'suc_2330 |
    C_load'45'from'45'slot_2332 Integer |
    C_store'45'at'45'slot_2334 Integer | C_store'45'indirect_2336 |
    C_store'45'indirect'45'suc_2338 | C_lea'45'slot_2340 Integer |
    C_restore'45'input_2342 Integer |
    C_instr'45'alloc'45'stack_2344 Integer |
    C_instr'45'dealloc'45'stack_2346 Integer |
    C_instr'45'reclaim'45'to_2348 Integer |
    C_instr'45'push'45'frame_2350 Integer |
    C_instr'45'pop'45'frame_2352 | C_instr'45'call'45'closure_2354 |
    C_worklist'45'init_2356 Integer | C_worklist'45'push_2358 Integer |
    C_worklist'45'pop_2360 Integer | C_worklist'45'check_2362 Integer |
    C_instr'45'sigop_2368 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.Spec.Type.T_Ty_8
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 |
    C_instr'45'load'45'const_2374 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                                  MAlonzo.Code.Once.Type.T_FitsInReg_24 AgdaAny |
    C_instr'45'load'45'code'45'addr_2376 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2378 |
    C_instr'45'load'45'tag'45'lit_2380 Integer |
    C_instr'45'alloc'45'heap_2382 Integer | C_instr'45'reg'45'op_2384 |
    C_instr'45'ctrl_2386 T_FlatCtrl_2298 |
    C_instr'45'free'45'heap_2388 Integer |
    C_instr'45'room_2390 Integer | C_load'45'at_2392 Integer |
    C_store'45'at_2394 Integer | C_addr'45'at_2396 Integer
-- Once.CCC.Machine.SMCore.CallI
d_CallI_2398 :: T_AbstractInstr_2322 -> ()
d_CallI_2398 = erased
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2400 :: ()
d_AbstractTrace_2400 = erased
-- Once.CCC.Machine.SMCore.CompUnit
d_CompUnit_2402 = ()
data T_CompUnit_2402
  = C_unit_2416 Integer [T_AbstractInstr_2322]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Machine.SMCore.CompUnit.entry-budget
d_entry'45'budget_2410 :: T_CompUnit_2402 -> Integer
d_entry'45'budget_2410 v0
  = case coe v0 of
      C_unit_2416 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.entry
d_entry_2412 :: T_CompUnit_2402 -> [T_AbstractInstr_2322]
d_entry_2412 v0
  = case coe v0 of
      C_unit_2416 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.blocks
d_blocks_2414 ::
  T_CompUnit_2402 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2414 v0
  = case coe v0 of
      C_unit_2416 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.block-layout
d_block'45'layout_2418 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_AbstractInstr_2322]
d_block'45'layout_2418 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_instr'45'ctrl_2386
                       (coe
                          C_c'45'entry_2306
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_instr'45'ctrl_2386 (coe C_c'45'ret_2308 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout
d_blocks'45'layout_2426 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_AbstractInstr_2322]
d_blocks'45'layout_2426 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_block'45'layout_2418 (coe v1))
             (coe d_blocks'45'layout_2426 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout-++
d_blocks'45'layout'45''43''43'_2436 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blocks'45'layout'45''43''43'_2436 = erased
-- Once.CCC.Machine.SMCore.link
d_link_2448 :: T_CompUnit_2402 -> [T_AbstractInstr_2322]
d_link_2448 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2412 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2386
            (coe C_c'45'ret_2308 (coe d_entry'45'budget_2410 (coe v0))))
         (coe d_blocks'45'layout_2426 (coe d_blocks_2414 (coe v0))))
-- Once.CCC.Machine.SMCore.link-top
d_link'45'top_2452 :: T_CompUnit_2402 -> [T_AbstractInstr_2322]
d_link'45'top_2452 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2412 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe C_instr'45'ctrl_2386 (coe C_c'45'leave_2314))
         (coe d_blocks'45'layout_2426 (coe d_blocks_2414 (coe v0))))
-- Once.CCC.Machine.SMCore.link-pre
d_link'45'pre_2456 ::
  T_CompUnit_2402 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> [T_AbstractInstr_2322]
d_link'45'pre_2456 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2412 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2386
            (coe C_c'45'ret_2308 (coe d_entry'45'budget_2410 (coe v0))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_blocks'45'layout_2426 (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  C_instr'45'ctrl_2386
                  (coe
                     C_c'45'entry_2306
                     (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
                     (coe v3)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMCore.link-post
d_link'45'post_2466 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [T_AbstractInstr_2322]
d_link'45'post_2466 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_instr'45'ctrl_2386 (coe C_c'45'ret_2308 (coe v1)))
      (coe d_blocks'45'layout_2426 (coe v0))
-- Once.CCC.Machine.SMCore.link-block-split
d_link'45'block'45'split_2484 ::
  T_CompUnit_2402 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2322] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_link'45'block'45'split_2484 = erased
-- Once.CCC.Machine.SMCore._.inner
d_inner_2504 ::
  T_CompUnit_2402 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2322] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_2504 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2512 = ()
data T_TreeTrace_2512
  = C_ε_2514 | C_instr_2516 T_AbstractInstr_2322 |
    C__'9656'__2518 T_TreeTrace_2512 T_TreeTrace_2512 |
    C_branch_2520 Integer T_TreeTrace_2512 T_TreeTrace_2512 |
    C_call'45'sub_2522 T_TreeTrace_2512 |
    C_flat_2524 [T_AbstractInstr_2322]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2526 :: [T_AbstractInstr_2322] -> T_TreeTrace_2512
d_flatToTree_2526 v0
  = case coe v0 of
      [] -> coe C_ε_2514
      (:) v1 v2
        -> coe
             C__'9656'__2518 (coe C_instr_2516 (coe v1))
             (coe d_flatToTree_2526 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2532 :: T_TreeTrace_2512 -> [T_AbstractInstr_2322]
d_treeToFlat_2532 v0
  = case coe v0 of
      C_ε_2514 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2516 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2518 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2532 (coe v1)) (coe d_treeToFlat_2532 (coe v2))
      C_branch_2520 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2532 (coe v2)) (coe d_treeToFlat_2532 (coe v3))
      C_call'45'sub_2522 v1 -> coe d_treeToFlat_2532 (coe v1)
      C_flat_2524 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2548 ::
  Integer -> T_TreeTrace_2512 -> [T_AbstractInstr_2322]
d_treeToRunnable_2548 v0 v1
  = case coe v1 of
      C_ε_2514 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2516 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2518 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2548 (coe v0) (coe v2))
             (coe d_treeToRunnable_2548 (coe v0) (coe v3))
      C_branch_2520 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2548 (coe v0) (coe v3))
             (coe d_treeToRunnable_2548 (coe v0) (coe v4))
      C_call'45'sub_2522 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2358 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2548 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2360 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2524 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2578 ::
  Integer -> T_TreeTrace_2512 -> [T_AbstractInstr_2322]
d_treeToRunnableWithInit_2578 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2356 (coe v0))
      (coe d_treeToRunnable_2548 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.in-memory?
d_in'45'memory'63'_2584 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_in'45'memory'63'_2584 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.in-memory-nofit
d_in'45'memory'45'nofit_2596 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in'45'memory'45'nofit_2596 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_clear'45'frame_2654 v0 = coe d_clear'45'frame_578 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
d_clear'45'frame'45'aux_2656 ~v0 = du_clear'45'frame'45'aux_2656
du_clear'45'frame'45'aux_2656 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 -> Maybe T_StoredValue_62
du_clear'45'frame'45'aux_2656 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_572 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2658 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2660 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_readHeapLoc_2660 v0 v1 = coe d_heapMem_276 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
d_readLoc_2662 ~v0 = du_readLoc_2662
du_readLoc_2662 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_62
du_readLoc_2662 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2664 ::
  T_LocState_254 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_readStackLoc_2664 v0 v1 v2 = coe d_stackMem_274 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
d_writeHeapMem_2666 ~v0 = du_writeHeapMem_2666
du_writeHeapMem_2666 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_62) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_62
du_writeHeapMem_2666 = coe du_writeHeapMem_660
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeHeapMem'45'aux_2668 ~v0 = du_writeHeapMem'45'aux_2668
du_writeHeapMem'45'aux_2668 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeHeapMem'45'aux_2668 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_654 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLoc_2670 v0 = coe d_writeLoc_688 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2672 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2674 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2674 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2676 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2678 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2678 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2680 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2682 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2684 ::
  T_LocState_254 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 ->
  T_Registers_116 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2684 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
d_writeLocToHeap_2686 ~v0 = du_writeLocToHeap_2686
du_writeLocToHeap_2686 ::
  T_LocState_254 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_62 -> T_LocState_254
du_writeLocToHeap_2686 = coe du_writeLocToHeap_680
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 ->
  AgdaAny -> Integer -> T_StoredValue_62 -> T_LocState_254
d_writeLocToStack_2688 v0 = coe d_writeLocToStack_670 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_62) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_62 -> AgdaAny -> Integer -> Maybe T_StoredValue_62
d_writeStackMem_2690 v0 = coe d_writeStackMem_550 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
d_writeStackMem'45'aux_2692 ~v0 = du_writeStackMem'45'aux_2692
du_writeStackMem'45'aux_2692 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_62 ->
  T_StoredValue_62 -> Maybe T_StoredValue_62
du_writeStackMem'45'aux_2692 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_542 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1274 -> T_LocState_254 -> T_LocState_254
d_exec_2696 v0 = coe d_exec_1592 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-addr-at-resolved
d_exec'45'addr'45'at'45'resolved_2698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'at'45'resolved_2698 ~v0
  = du_exec'45'addr'45'at'45'resolved_2698
du_exec'45'addr'45'at'45'resolved_2698 ::
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'at'45'resolved_2698
  = coe du_exec'45'addr'45'at'45'resolved_1458
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-addr-in-block
d_exec'45'addr'45'in'45'block_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'addr'45'in'45'block_2700 ~v0
  = du_exec'45'addr'45'in'45'block_2700
du_exec'45'addr'45'in'45'block_2700 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'addr'45'in'45'block_2700
  = coe du_exec'45'addr'45'in'45'block_1450
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-at-resolved
d_exec'45'load'45'at'45'resolved_2702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'at'45'resolved_2702 ~v0
  = du_exec'45'load'45'at'45'resolved_2702
du_exec'45'load'45'at'45'resolved_2702 ::
  Integer ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'at'45'resolved_2702
  = coe du_exec'45'load'45'at'45'resolved_1398
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_62 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2704 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_254 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2706 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'suc'45'via'45'resolved_2708 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2708
du_exec'45'load'45'suc'45'via'45'resolved_2708 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'suc'45'via'45'resolved_2708
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1376
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_exec'45'load'45'via'45'resolved_2710 ~v0
  = du_exec'45'load'45'via'45'resolved_2710
du_exec'45'load'45'via'45'resolved_2710 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
du_exec'45'load'45'via'45'resolved_2710
  = coe du_exec'45'load'45'via'45'resolved_1354
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'load'45'with'45'value_2712 ~v0
  = du_exec'45'load'45'with'45'value_2712
du_exec'45'load'45'with'45'value_2712 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
du_exec'45'load'45'with'45'value_2712
  = coe du_exec'45'load'45'with'45'value_1342
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-at-resolved
d_exec'45'store'45'at'45'resolved_2714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'at'45'resolved_2714 v0
  = coe d_exec'45'store'45'at'45'resolved_1432 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-in-block
d_exec'45'store'45'in'45'block_2716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'in'45'block_2716 v0
  = coe d_exec'45'store'45'in'45'block_1422 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'suc'45'via'45'resolved_2718 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1388 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62 -> T_LocState_254 -> T_LocState_254
d_exec'45'store'45'via'45'resolved_2720 v0
  = coe d_exec'45'store'45'via'45'resolved_1366 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1274] -> T_LocState_254 -> T_LocState_254
d_execList_2722 v0 = coe d_execList_1626 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.frame-gate
d_frame'45'gate_2724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_frame'45'gate_2724 v0 = coe d_frame'45'gate_1498 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.gate-or
d_gate'45'or_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_gate'45'or_2726 v0 = coe d_gate'45'or_1548 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.heap-gate
d_heap'45'gate_2728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'gate_2728 ~v0 = du_heap'45'gate_2728
du_heap'45'gate_2728 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'gate_2728 = coe du_heap'45'gate_1518
-- Once.CCC.Machine.SMCore.AbstractExec._.in-block?
d_in'45'block'63'_2730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
d_in'45'block'63'_2730 ~v0 = du_in'45'block'63'_2730
du_in'45'block'63'_2730 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> Bool
du_in'45'block'63'_2730 = coe du_in'45'block'63'_1414
-- Once.CCC.Machine.SMCore.AbstractExec._.in-window
d_in'45'window_2732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Integer -> Bool
d_in'45'window_2732 v0 = coe d_in'45'window_1478 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.live-frames
d_live'45'frames_2734 ::
  T_AllocState_348 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_live'45'frames_2734 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_current'45'frame_448 (coe v0))
         (coe d_frame'45'slots_452 (coe v0)))
      (coe d_saved'45'frames_450 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec._.range-ok
d_range'45'ok_2736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> T_StoredValue_62 -> Bool
d_range'45'ok_2736 v0 = coe d_range'45'ok_1564 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate
d_stack'45'gate_2738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'gate_2738 ~v0 = du_stack'45'gate_2738
du_stack'45'gate_2738 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'gate_2738 = coe du_stack'45'gate_1494
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate-or
d_stack'45'gate'45'or_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stack'45'gate'45'or_2740 ~v0 = du_stack'45'gate'45'or_2740
du_stack'45'gate'45'or_2740 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_stack'45'gate'45'or_2740 v0 v1
  = coe du_stack'45'gate'45'or_1526 v0
-- Once.CCC.Machine.SMCore.AbstractExec._.stack-gate-true
d_stack'45'gate'45'true_2742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'gate'45'true_2742 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2744 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2744 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2744 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2744 v0 v1 v2
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
d_exec'45'restore'45'input'45'with'45'value_2756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2756 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2756 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2756 ::
  Maybe T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2756 v0 v1 v2
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
d_exec'45'load'45'from'45'slot'45'just_2774 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2774 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2780 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2780 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2788 ::
  T_StoredValue_62 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2788 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2794 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2794 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62
d_unit'45'storedvalue_2796 ~v0 = du_unit'45'storedvalue_2796
du_unit'45'storedvalue_2796 :: T_StoredValue_62
du_unit'45'storedvalue_2796
  = coe
      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2802 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2802 v3 v4
du_combine'45'typed_2802 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2802 v0 v1
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
d_readTyped'45'int_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'int_2808 ~v0 v1 = du_readTyped'45'int_2808 v1
du_readTyped'45'int_2808 :: Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'int_2808 v0
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
d_readTyped'45'float_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_62 -> Maybe Integer
d_readTyped'45'float_2812 ~v0 v1 = du_readTyped'45'float_2812 v1
du_readTyped'45'float_2812 ::
  Maybe T_StoredValue_62 -> Maybe Integer
du_readTyped'45'float_2812 v0
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
d_readTyped'45'cell_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
d_readTyped'45'cell_2818 ~v0 ~v1 v2 v3 v4
  = du_readTyped'45'cell_2818 v2 v3 v4
du_readTyped'45'cell_2818 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 -> Maybe AgdaAny
du_readTyped'45'cell_2818 v0 v1 v2
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
d_readTyped'45'pair_2854 ::
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
d_readTyped'45'pair_2854 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_readTyped'45'pair_2854 v3 v4 v5 v6 v7 v8
du_readTyped'45'pair_2854 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  (T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2854 v0 v1 v2 v3 v4 v5
  = coe
      du_combine'45'typed_2802
      (coe du_readTyped'45'cell_2818 (coe v0) (coe v2) (coe v4))
      (coe du_readTyped'45'cell_2818 (coe v1) (coe v3) (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
d_readReg'45'typed_2870 ~v0 v1 v2 = du_readReg'45'typed_2870 v1 v2
du_readReg'45'typed_2870 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_StoredValue_62 -> Maybe AgdaAny
du_readReg'45'typed_2870 v0 v1
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
d_readTyped'45'sum_2880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_2880 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'sum_2880 v3 v4 v5 v6
du_readTyped'45'sum_2880 ::
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_62 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_62 ->
  Maybe T_StoredValue_62 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_2880 v0 v1 v2 v3
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
d_tsize_2924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_tsize_2924 ~v0 v1 = du_tsize_2924 v1
du_tsize_2924 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_tsize_2924 v0
  = let v1 = 1 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe (0 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe (0 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe
                addInt (coe du_tsize_2924 (coe v2)) (coe du_tsize_2924 (coe v3))
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
           -> coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe du_tsize_2924 (coe v2)) (coe du_tsize_2924 (coe v3)))
         MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (1 :: Integer)
         MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (1 :: Integer)
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_2936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
d_readTyped_2936 ~v0 v1 v2 v3 = du_readTyped_2936 v1 v2 v3
du_readTyped_2936 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> Maybe AgdaAny
du_readTyped_2936 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
           -> coe
                du_combine'45'typed_2802
                (coe du_readTyped_2936 (coe v4) (coe v1) (coe v2))
                (coe
                   du_readTyped_2936 (coe v5)
                   (coe du_offsetLoc_88 (coe v1) (coe du_tsize_2924 (coe v4)))
                   (coe v2))
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
           -> coe
                du_readTyped'45'sum_2880
                (coe
                   (\ v6 ->
                      coe
                        du_readTyped_2936 (coe v4) (coe du_sucLoc_78 (coe v1)) (coe v2)))
                (coe
                   (\ v6 ->
                      coe
                        du_readTyped_2936 (coe v5) (coe du_sucLoc_78 (coe v1)) (coe v2)))
                (coe du_readLoc_522 (coe v2) (coe v1))
                (coe du_readLoc_522 (coe v2) (coe du_sucLoc_78 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> coe
                du_readTyped'45'int_2808 (coe du_readLoc_522 (coe v2) (coe v1))
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> coe
                du_readTyped'45'float_2812 (coe du_readLoc_522 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.zero-word
d_zero'45'word_2974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_62
d_zero'45'word_2974 ~v0 = du_zero'45'word_2974
du_zero'45'word_2974 :: T_StoredValue_62
du_zero'45'word_2974
  = coe
      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.writeZeros
d_writeZeros_2976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_writeZeros_2976 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_writeZeros_2976 (coe v0) (coe v4) (coe du_sucLoc_78 (coe v2))
                (coe
                   d_writeLoc_688 (coe v0) (coe v3) (coe v2)
                   (coe du_zero'45'word_2974)))
-- Once.CCC.Machine.SMCore.AbstractExec.writeTyped
d_writeTyped_2990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> T_LocState_254
d_writeTyped_2990 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v4
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d_writeTyped_2990 (coe v0) (coe v6) (coe v8)
                    (coe du_offsetLoc_88 (coe v3) (coe du_tsize_2924 (coe v5)))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v5) (coe v7) (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    d_writeZeros_2976 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_2924 (coe v5)) (coe du_tsize_2924 (coe v6)))
                       (coe du_tsize_2924 (coe v5)))
                    (coe
                       du_offsetLoc_88 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_2924 (coe v5))))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v5) (coe v7)
                       (coe du_sucLoc_78 (coe v3))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v4) (coe v3)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer)))))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    d_writeZeros_2976 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_2924 (coe v5)) (coe du_tsize_2924 (coe v6)))
                       (coe du_tsize_2924 (coe v6)))
                    (coe
                       du_offsetLoc_88 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_2924 (coe v6))))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v6) (coe v7)
                       (coe du_sucLoc_78 (coe v3))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v4) (coe v3)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             d_writeLoc_688 (coe v0) (coe v4) (coe v3)
             (coe
                C_SV'45'Lit_72 (coe v1)
                (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             d_writeLoc_688 (coe v0) (coe v4) (coe v3)
             (coe
                C_SV'45'Lit_72 (coe v1)
                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v2))
      _ -> coe v4
-- Once.CCC.Machine.SMCore.AbstractExec.PlainWord
d_PlainWord_3044 a0 a1 = ()
data T_PlainWord_3044 = C_pw'45'lit_3052 | C_pw'45'tag_3056
-- Once.CCC.Machine.SMCore.AbstractExec.zeros-keeps
d_zeros'45'keeps_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_zeros'45'keeps_3072 v0 ~v1 v2 v3 v4 v5 v6
  = du_zeros'45'keeps_3072 v0 v2 v3 v4 v5 v6
du_zeros'45'keeps_3072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_zeros'45'keeps_3072 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      0 -> coe v5
      _ -> let v6 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                du_zeros'45'keeps_3072 (coe v0) (coe v1) (coe v6)
                (coe du_sucLoc_78 (coe v3))
                (coe
                   d_writeLoc_688 (coe v0) (coe v4) (coe v3)
                   (coe
                      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26)
                      (coe (0 :: Integer))))
                (coe
                   v1 v4 v3
                   (coe
                      C_SV'45'Lit_72 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                      (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe (0 :: Integer)))
                   (coe C_pw'45'lit_3052) v5))
-- Once.CCC.Machine.SMCore.AbstractExec.writeTyped-keeps
d_writeTyped'45'keeps_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_writeTyped'45'keeps_3112 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_writeTyped'45'keeps_3112 v0 v2 v3 v4 v5 v6 v7
du_writeTyped'45'keeps_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_writeTyped'45'keeps_3112 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v7 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v6
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_writeTyped'45'keeps_3112 (coe v0) (coe v1) (coe v8) (coe v10)
                    (coe du_offsetLoc_88 (coe v4) (coe du_tsize_2924 (coe v7)))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v7) (coe v9) (coe v4) (coe v5))
                    (coe
                       du_writeTyped'45'keeps_3112 (coe v0) (coe v1) (coe v7) (coe v9)
                       (coe v4) (coe v5) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> coe
                    du_zeros'45'keeps_3072 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_2924 (coe v7)) (coe du_tsize_2924 (coe v8)))
                       (coe du_tsize_2924 (coe v7)))
                    (coe
                       du_offsetLoc_88 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_2924 (coe v7))))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v7) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer)))))
                    (coe
                       du_writeTyped'45'keeps_3112 (coe v0) (coe v1) (coe v7) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (0 :: Integer))))
                       (coe
                          v1 v5 v4 (coe C_SV'45'Tag_68 (coe (0 :: Integer)))
                          (coe C_pw'45'tag_3056) v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> coe
                    du_zeros'45'keeps_3072 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                          (coe du_tsize_2924 (coe v7)) (coe du_tsize_2924 (coe v8)))
                       (coe du_tsize_2924 (coe v8)))
                    (coe
                       du_offsetLoc_88 (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe du_tsize_2924 (coe v8))))
                    (coe
                       d_writeTyped_2990 (coe v0) (coe v8) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer)))))
                    (coe
                       du_writeTyped'45'keeps_3112 (coe v0) (coe v1) (coe v8) (coe v9)
                       (coe du_sucLoc_78 (coe v4))
                       (coe
                          d_writeLoc_688 (coe v0) (coe v5) (coe v4)
                          (coe C_SV'45'Tag_68 (coe (1 :: Integer))))
                       (coe
                          v1 v5 v4 (coe C_SV'45'Tag_68 (coe (1 :: Integer)))
                          (coe C_pw'45'tag_3056) v6))
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
             (coe C_pw'45'lit_3052) v6
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             v1 v5 v4
             (coe
                C_SV'45'Lit_72 (coe v2)
                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v3))
             (coe C_pw'45'lit_3052) v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_3264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_structured'45'pure'45'sigop'45'output_3264 ~v0 ~v1 ~v2 ~v3 v4
  = du_structured'45'pure'45'sigop'45'output_3264 v4
du_structured'45'pure'45'sigop'45'output_3264 ::
  T_LocState_254 -> T_StoredValue_62
du_structured'45'pure'45'sigop'45'output_3264 v0
  = coe du_readReg_132 (coe d_regs_272 (coe v0)) (coe C_Output_58)
-- Once.CCC.Machine.SMCore.AbstractExec.decode-at
d_decode'45'at_3272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
d_decode'45'at_3272 ~v0 v1 v2 v3 v4
  = du_decode'45'at_3272 v1 v2 v3 v4
du_decode'45'at_3272 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  T_StoredValue_62 -> T_LocState_254 -> Maybe AgdaAny
du_decode'45'at_3272 v0 v1 v2 v3
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
                         -> coe du_readTyped_2936 (coe v0) (coe v11) (coe v3)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v7 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                  -> case coe v2 of
                       C_SV'45'Ptr_66 v11
                         -> coe du_readTyped_2936 (coe v0) (coe v11) (coe v3)
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.events-at-arg
d_events'45'at'45'arg_3294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_events'45'at'45'arg_3294 ~v0 v1 ~v2 v3 v4
  = du_events'45'at'45'arg_3294 v1 v3 v4
du_events'45'at'45'arg_3294 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_events'45'at'45'arg_3294 v0 v1 v2
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
d_machine'45'events_3308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_machine'45'events_3308 ~v0 v1 ~v2 v3 v4
  = du_machine'45'events_3308 v1 v3 v4
du_machine'45'events_3308 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_machine'45'events_3308 v0 v1 v2
  = coe
      du_events'45'at'45'arg_3294 (coe v0) (coe v1)
      (coe
         du_decode'45'at_3272 (coe v0)
         (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v1))
         (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))
         (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_3320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> T_StoredValue_62
d_call'45'sigop'45'ans'45'at_3320 v0 v1 v2 v3 v4 v5 v6 v7
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
        -> coe du_unit'45'storedvalue_2796
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_3350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_StoredValue_62
d_call'45'sigop'45'ans_3350 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           d_call'45'sigop'45'ans'45'at_3320 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v9)
                           (coe
                              du_decode'45'at_3272 (coe v1)
                              (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v3))
                              (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56))
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v8) (coe du_unit'45'storedvalue_2796)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_3372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_3372 v0 v1 v2 v3
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
d_call'45'sigop'45'val_3384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 -> T_StoredValue_62
d_call'45'sigop'45'val_3384 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_call'45'sigop'45'ans_3350 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe
                d_call'45'sigop'45'dec_3372 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Output_58)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_3400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_call'45'sigop'45'output_3400 v0 v1 v2 v3 v4
  = coe
      d_call'45'sigop'45'val_3384 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_3412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_pure'45'sigop'45'output_3412 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_3442 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_32 (coe v2))
      (coe
         du_sv'45'as'45'loc_1238
         (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_3418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe AgdaAny -> T_StoredValue_62
d_pure'45'sigop'45'out'45'val_3418 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_res'45'sv_3422 (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_206 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_182 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                   (coe v0))
                v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2796
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.res-sv
d_res'45'sv_3422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
d_res'45'sv_3422 ~v0 v1 v2 v3 = du_res'45'sv_3422 v1 v2 v3
du_res'45'sv_3422 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_62
du_res'45'sv_3422 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe du_unit'45'storedvalue_2796
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe C_SV'45'Lit_72 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_24 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_62
d_pure'45'sigop'45'out'45'aux_3442 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    d_pure'45'sigop'45'out'45'val_3418 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe du_readTyped_2936 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    d_pure'45'sigop'45'out'45'val_3418 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2870 (coe v1)
                       (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_structured'45'pure'45'sigop'45'output_3264 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output'45'of_3478 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             d_pure'45'sigop'45'output_3412 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_unit'45'storedvalue_2796
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_unit'45'storedvalue_2796
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             d_call'45'sigop'45'output_3400 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_3492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events'45'of_3492 ~v0 v1 ~v2 v3 v4 v5
  = du_sigop'45'events'45'of_3492 v1 v3 v4 v5
du_sigop'45'events'45'of_3492 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events'45'of_3492 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe du_machine'45'events_3308 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe du_machine'45'events_3308 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe du_machine'45'events_3308 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events
d_sigop'45'events_3510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_sigop'45'events_3510 ~v0 v1 ~v2 v3 v4
  = du_sigop'45'events_3510 v1 v3 v4
du_sigop'45'events_3510 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_sigop'45'events_3510 v0 v1 v2
  = coe
      du_sigop'45'events'45'of_3492 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_3520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_StoredValue_62
d_exec'45'sigop'45'output_3520 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_3478 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.unread?
d_unread'63'_3528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Maybe AgdaAny -> Bool
d_unread'63'_3528 ~v0 ~v1 v2 = du_unread'63'_3528 v2
du_unread'63'_3528 :: Maybe AgdaAny -> Bool
du_unread'63'_3528 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-faults-of
d_exec'45'sigop'45'faults'45'of_3534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'faults'45'of_3534 ~v0 v1 ~v2 v3 v4 v5
  = du_exec'45'sigop'45'faults'45'of_3534 v1 v3 v4 v5
du_exec'45'sigop'45'faults'45'of_3534 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'faults'45'of_3534 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             du_unread'63'_3528
             (coe
                du_decode'45'at_3272 (coe v0)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v2))
                (coe du_readReg_132 (coe d_regs_272 (coe v3)) (coe C_Input1_56))
                (coe v3))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-faults
d_exec'45'sigop'45'faults_3544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'faults_3544 ~v0 v1 ~v2 v3 v4
  = du_exec'45'sigop'45'faults_3544 v1 v3 v4
du_exec'45'sigop'45'faults_3544 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'faults_3544 v0 v1 v2
  = coe
      du_exec'45'sigop'45'faults'45'of_3534 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts'45'of_3554 ~v0 v1 ~v2 v3 v4 v5
  = du_exec'45'sigop'45'halts'45'of_3554 v1 v3 v4 v5
du_exec'45'sigop'45'halts'45'of_3554 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'halts'45'of_3554 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             du_exec'45'sigop'45'faults'45'of_3534 (coe v0) (coe v1) (coe v2)
             (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_3564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_exec'45'sigop'45'halts_3564 ~v0 v1 ~v2 v3 v4
  = du_exec'45'sigop'45'halts_3564 v1 v3 v4
du_exec'45'sigop'45'halts_3564 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
du_exec'45'sigop'45'halts_3564 v0 v1 v2
  = coe
      du_exec'45'sigop'45'halts'45'of_3554 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.res-just
d_res'45'just_3572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> Maybe AgdaAny
d_res'45'just_3572 ~v0 ~v1 v2 = du_res'45'just_3572 v2
du_res'45'just_3572 ::
  MAlonzo.Code.Once.Res.T_Res_6 -> Maybe AgdaAny
du_res'45'just_3572 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Res.C_returns_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-ans-at
d_call'45'ans'45'at_3582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny -> Maybe AgdaAny
d_call'45'ans'45'at_3582 v0 v1 v2 v3 v4 v5 v6
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
d_pure'45'ans'45'at_3610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe AgdaAny -> Maybe AgdaAny
d_pure'45'ans'45'at_3610 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_res'45'just_3572
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_206 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_182 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_186
                   (coe v0))
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-answer-of
d_sigop'45'answer'45'of_3622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_58 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Maybe AgdaAny
d_sigop'45'answer'45'of_3622 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_62
        -> coe
             d_pure'45'ans'45'at_3610 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                du_decode'45'at_3272 (coe v1)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56))
                (coe v5))
      MAlonzo.Code.Once.SigOp.Info.C_Emits_64
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_Halts_66
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.SigOp.Info.C_Answers_68
        -> coe
             d_call'45'ans'45'at_3582 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
             (coe
                d_call'45'sigop'45'dec_3372 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe
                du_decode'45'at_3272 (coe v1)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-answer
d_sigop'45'answer_3636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Maybe AgdaAny
d_sigop'45'answer_3636 v0 v1 v2 v3 v4
  = coe
      d_sigop'45'answer'45'of_3622 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_216 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-at
d_sigop'45'store'45'at_3644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> T_LocState_254 -> T_LocState_254
d_sigop'45'store'45'at_3644 v0 v1 v2 v3 v4 v5
  = if coe v2
      then case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                      -> coe
                           d_writeTyped_2990 (coe v0) (coe v1) (coe v7) (coe v6) (coe v5)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe v5
-- Once.CCC.Machine.SMCore.AbstractExec.arg-words
d_arg'45'words_3664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
d_arg'45'words_3664 ~v0 v1 v2 = du_arg'45'words_3664 v1 v2
du_arg'45'words_3664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> Integer
du_arg'45'words_3664 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v5 v6
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
                  -> coe du_tsize_2924 (coe v0)
                _ -> coe v2
         MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v5 v6
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
                  -> coe du_tsize_2924 (coe v0)
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.ans-words
d_ans'45'words_3670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_ans'45'words_3670 ~v0 v1 = du_ans'45'words_3670 v1
du_ans'45'words_3670 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_ans'45'words_3670 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_in'45'memory'63'_2584 (coe v0)) (coe du_tsize_2924 (coe v0))
      (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-gate
d_sigop'45'gate_3678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_AllocState_348 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> Bool
d_sigop'45'gate_3678 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         d_range'45'ok_1564 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe d_current'45'frame_448 (coe v3))
               (coe d_frame'45'slots_452 (coe v3)))
            (coe d_saved'45'frames_450 (coe v3)))
         (coe
            du_arg'45'words_3664 (coe v1)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe v4)))
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Input1_56)))
      (coe
         d_range'45'ok_1564 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe d_current'45'frame_448 (coe v3))
               (coe d_frame'45'slots_452 (coe v3)))
            (coe d_saved'45'frames_450 (coe v3)))
         (coe du_ans'45'words_3670 (coe v2))
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Output_58)))
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store
d_sigop'45'store_3694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> T_LocState_254
d_sigop'45'store_3694 v0 v1 v2 v3 v4
  = coe
      d_sigop'45'store'45'at_3644 (coe v0) (coe v2)
      (coe d_in'45'memory'63'_2584 (coe v2))
      (coe
         du_sv'45'as'45'loc_1238
         (coe du_readReg_132 (coe d_regs_272 (coe v4)) (coe C_Output_58)))
      (coe
         d_sigop'45'answer_3636 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-keeps
d_sigop'45'store'45'keeps_3718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
d_sigop'45'store'45'keeps_3718 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_sigop'45'store'45'keeps_3718 v0 v2 v3 v4 v5 v6 v7
du_sigop'45'store'45'keeps_3718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 -> AgdaAny -> AgdaAny
du_sigop'45'store'45'keeps_3718 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_go_3742 (coe v0) (coe v1) (coe v3) (coe v5) (coe v6)
      (coe d_in'45'memory'63'_2584 (coe v3))
      (coe
         du_sv'45'as'45'loc_1238
         (coe du_readReg_132 (coe d_regs_272 (coe v5)) (coe C_Output_58)))
      (coe
         d_sigop'45'answer_3636 (coe v0) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec._.go
d_go_3742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 -> ()) ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  AgdaAny ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> AgdaAny
d_go_3742 v0 ~v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10
  = du_go_3742 v0 v2 v4 v6 v7 v8 v9 v10
du_go_3742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_254 ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   T_StoredValue_62 -> T_PlainWord_3044 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_LocState_254 ->
  AgdaAny ->
  Bool ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe AgdaAny -> AgdaAny
du_go_3742 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v5
      then case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> coe
                           du_writeTyped'45'keeps_3112 (coe v0) (coe v1) (coe v2) (coe v9)
                           (coe v8) (coe v3) (coe v4)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe v4
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-store-id
d_sigop'45'store'45'id_3758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'store'45'id_3758 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.go
d_go_3774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  T_LocState_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3774 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.lit-value
d_lit'45'value_3780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
d_lit'45'value_3780 v0 ~v1 v2 v3 = du_lit'45'value_3780 v0 v2 v3
du_lit'45'value_3780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_24 -> AgdaAny -> AgdaAny
du_lit'45'value_3780 v0 v1 v2
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
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_3786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2322 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_3786 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2324
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
      C_mov'45'to'45'input_2326
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
      C_load'45'indirect_2328
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1354 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2330
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1376 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2332 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2744
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2334 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_688 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2336
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1366 v0
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2338
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1388 v0
                (coe
                   du_sv'45'as'45'loc_1238
                   (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2340 v4
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
      C_restore'45'input_2342 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2756
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2344 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'dealloc'45'stack_2346 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2348 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'push'45'frame_2350 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2352
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2354
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2356 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2358 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_688 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2360 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2744
             (coe
                du_readLoc_522 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_448 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2362 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2368 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_3520
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe
                   d_stackMem_274
                   (coe
                      d_sigop'45'store_3694 (coe v0) (coe v4) (coe v5) (coe v6)
                      (coe v2)))
                (coe
                   d_heapMem_276
                   (coe
                      d_sigop'45'store_3694 (coe v0) (coe v4) (coe v5) (coe v6)
                      (coe v2)))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe du_exec'45'sigop'45'halts_3564 (coe v4) (coe v6) (coe v2))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d_not_22
                      (coe
                         d_sigop'45'gate_3678 (coe v0) (coe v4) (coe v5) (coe v3) (coe v6)
                         (coe v2))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_ev'45'log_280 (coe v2))
                   (coe du_sigop'45'events_3510 (coe v4) (coe v6) (coe v2)))
                (coe d_left_282 (coe v2))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe du_exec'45'sigop'45'faults_3544 (coe v4) (coe v6) (coe v2))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d_not_22
                         (coe
                            d_sigop'45'gate_3678 (coe v0) (coe v4) (coe v5) (coe v3) (coe v6)
                            (coe v2)))
                      (coe d_faulted_284 (coe v2)))))
             (coe v3)
      C_instr'45'load'45'const_2374 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_286
                (coe
                   du_writeReg_140 (d_regs_272 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_72 (coe v4) (coe v5)
                      (coe du_lit'45'value_3780 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_274 (coe v2)) (coe d_heapMem_276 (coe v2))
                (coe d_halted_278 (coe v2)) (coe d_ev'45'log_280 (coe v2))
                (coe d_left_282 (coe v2)) (coe d_faulted_284 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2376 v4
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
      C_instr'45'save'45'closure'45'reg_2378
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2380 v4
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
      C_instr'45'alloc'45'heap_2382 v4
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
      C_instr'45'reg'45'op_2384
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_302 (coe v2)) (coe v3)
      C_instr'45'ctrl_2386 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'free'45'heap_2388 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'room_2390 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_load'45'at_2392 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'at'45'resolved_1398 v4 (coe C_Output_58)
                (d_frame'45'gate_1498
                   (coe v0) (coe v3) (coe v4)
                   (coe
                      du_sv'45'as'45'loc_1238
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                v2)
             (coe v3)
      C_store'45'at_2394 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'at'45'resolved_1432 v0
                (d_block'45'size_458 (coe v3)) v4
                (d_frame'45'gate_1498
                   (coe v0) (coe v3) (coe v4)
                   (coe
                      du_sv'45'as'45'loc_1238
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_addr'45'at_2396 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'addr'45'at'45'resolved_1458
                (d_block'45'size_458 (coe v3)) v4
                (coe
                   du_heap'45'gate_1518
                   (coe
                      du_sv'45'as'45'loc_1238
                      (coe du_readReg_132 (coe d_regs_272 (coe v2)) (coe C_Input1_56))))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_3788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2322] ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_3788 v0 v1 v2 v3
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
                       d_exec'45'trace_3788 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_3786 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_3786 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_4024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2322 ->
  [T_AbstractInstr_2322] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_4024 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_4070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2322 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_4070 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_4104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
d_getTag_4104 ~v0 v1 v2 v3 = du_getTag_4104 v1 v2 v3
du_getTag_4104 ::
  T_LocState_254 -> T_AllocState_348 -> Integer -> Maybe Integer
du_getTag_4104 v0 v1 v2
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
d_exec'45'tree'45'trace_4128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2512 ->
  T_LocState_254 ->
  T_AllocState_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_4128 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2514
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2516 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_3786 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2518 v4 v5
        -> let v6 = d_halted_278 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_4128 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_4128 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_4128 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2520 v4 v5 v6
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
                                            d_exec'45'tree'45'trace_4128 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_4128 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_4128 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_4128 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_4128 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2522 v4
        -> let v5 = d_halted_278 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_4128 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2524 v4
        -> coe d_exec'45'trace_3788 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_4288 ::
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_4288 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_4306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2512 ->
  T_TreeTrace_2512 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_4306 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_4352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2322 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_4352 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_4392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2512 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_4392 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_4432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2322] ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_4432 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_4446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2512 ->
  T_LocState_254 ->
  T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_4446 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_4446
du_exec'45'tree'45'flat'45'equiv'45'simple_4446 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_4446
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
