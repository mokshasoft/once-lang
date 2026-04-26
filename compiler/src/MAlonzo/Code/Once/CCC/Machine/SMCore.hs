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
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Machine.SMCore.just-injective
d_just'45'injective_14 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injective_14 = erased
-- Once.CCC.Machine.SMCore.Slot
d_Slot_16 :: ()
d_Slot_16 = erased
-- Once.CCC.Machine.SMCore.HeapOffset
d_HeapOffset_18 :: ()
d_HeapOffset_18 = erased
-- Once.CCC.Machine.SMCore.HeapRef
d_HeapRef_20 = ()
newtype T_HeapRef_20 = C_mkHeapRef_26 Integer
-- Once.CCC.Machine.SMCore.HeapRef.ref-id
d_ref'45'id_24 :: T_HeapRef_20 -> Integer
d_ref'45'id_24 v0
  = case coe v0 of
      C_mkHeapRef_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore._≟H_
d__'8799'H__32 ::
  T_HeapRef_20 ->
  T_HeapRef_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'H__32 v0 v1
  = case coe v0 of
      C_mkHeapRef_26 v2
        -> case coe v1 of
             C_mkHeapRef_26 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe v2))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                               (coe eqInt (coe v2) (coe v3))) in
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
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapLocation
d_HeapLocation_54 = ()
data T_HeapLocation_54 = C_heap'45'loc_64 T_HeapRef_20 Integer
-- Once.CCC.Machine.SMCore.HeapLocation.heap-ref
d_heap'45'ref_60 :: T_HeapLocation_54 -> T_HeapRef_20
d_heap'45'ref_60 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapLocation.heap-offset
d_heap'45'offset_62 :: T_HeapLocation_54 -> Integer
d_heap'45'offset_62 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.≟HL-aux
d_'8799'HL'45'aux_74 ::
  T_HeapRef_20 ->
  T_HeapRef_20 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'HL'45'aux_74 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'HL'45'aux_74 v4 v5
du_'8799'HL'45'aux_74 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'HL'45'aux_74 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore._≟HL_
d__'8799'HL__92 ::
  T_HeapLocation_54 ->
  T_HeapLocation_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__92 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> case coe v1 of
             C_heap'45'loc_64 v4 v5
               -> coe
                    du_'8799'HL'45'aux_74 (coe d__'8799'H__32 (coe v2) (coe v4))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.hl-ref
d_hl'45'ref_102 :: T_HeapLocation_54 -> T_HeapRef_20
d_hl'45'ref_102 v0 = coe d_heap'45'ref_60 (coe v0)
-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_104 = ()
data T_HeapRegion_104 = C_heap'45'region_114 T_HeapRef_20 Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_110 :: T_HeapRegion_104 -> T_HeapRef_20
d_region'45'ref_110 v0
  = case coe v0 of
      C_heap'45'region_114 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_112 :: T_HeapRegion_104 -> Integer
d_region'45'size_112 v0
  = case coe v0 of
      C_heap'45'region_114 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_116 a0 a1 = ()
newtype T_InRegion_116
  = C_in'45'region_124 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_126 :: ()
d_HeapOwnership_126 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_128 a0 a1 = ()
data T_OutsideOwned_128
  = C_outside'45'nil_132 |
    C_outside'45'cons_140 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                          T_OutsideOwned_128
-- Once.CCC.Machine.SMCore.ValueLocation
d_ValueLocation_144 a0 = ()
data T_ValueLocation_144
  = C_OnStack_148 AgdaAny Integer | C_OnHeap_150 T_HeapLocation_54
-- Once.CCC.Machine.SMCore.sucHL
d_sucHL_152 :: T_HeapLocation_54 -> T_HeapLocation_54
d_sucHL_152 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2
        -> coe
             C_heap'45'loc_64 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetHL
d_offsetHL_158 :: T_HeapLocation_54 -> Integer -> T_HeapLocation_54
d_offsetHL_158 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> coe C_heap'45'loc_64 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_144 -> T_ValueLocation_144
d_sucLoc_168 ~v0 v1 = du_sucLoc_168 v1
du_sucLoc_168 :: T_ValueLocation_144 -> T_ValueLocation_144
du_sucLoc_168 v0
  = case coe v0 of
      C_OnStack_148 v1 v2
        -> coe
             C_OnStack_148 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_OnHeap_150 v1 -> coe C_OnHeap_150 (coe d_sucHL_152 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_144 -> Integer -> T_ValueLocation_144
d_offsetLoc_178 ~v0 v1 v2 = du_offsetLoc_178 v1 v2
du_offsetLoc_178 ::
  T_ValueLocation_144 -> Integer -> T_ValueLocation_144
du_offsetLoc_178 v0 v1
  = case coe v0 of
      C_OnStack_148 v2 v3
        -> coe C_OnStack_148 (coe v2) (coe addInt (coe v1) (coe v3))
      C_OnHeap_150 v2
        -> coe C_OnHeap_150 (coe d_offsetHL_158 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_192 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_196 :: ()
d_HeapMem_196 = erased
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_198 = ()
data T_AbstractReg_198 = C_Input_200 | C_Output_202
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__208 ::
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__208 v0 v1
  = case coe v0 of
      C_Input_200
        -> case coe v1 of
             C_Input_200
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_202
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_202
        -> case coe v1 of
             C_Input_200
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_202
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_212 a0 = ()
data T_Registers_212
  = C_mkRegs_228 T_ValueLocation_144 T_ValueLocation_144 Integer
-- Once.CCC.Machine.SMCore.Registers.input
d_input_222 :: T_Registers_212 -> T_ValueLocation_144
d_input_222 v0
  = case coe v0 of
      C_mkRegs_228 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_224 :: T_Registers_212 -> T_ValueLocation_144
d_output_224 v0
  = case coe v0 of
      C_mkRegs_228 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_226 :: T_Registers_212 -> Integer
d_stackSlot_226 v0
  = case coe v0 of
      C_mkRegs_228 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 -> T_AbstractReg_198 -> T_ValueLocation_144
d_readReg_232 ~v0 v1 v2 = du_readReg_232 v1 v2
du_readReg_232 ::
  T_Registers_212 -> T_AbstractReg_198 -> T_ValueLocation_144
du_readReg_232 v0 v1
  = case coe v1 of
      C_Input_200 -> coe d_input_222 (coe v0)
      C_Output_202 -> coe d_output_224 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 ->
  T_AbstractReg_198 -> T_ValueLocation_144 -> T_Registers_212
d_writeReg_240 ~v0 v1 v2 = du_writeReg_240 v1 v2
du_writeReg_240 ::
  T_Registers_212 ->
  T_AbstractReg_198 -> T_ValueLocation_144 -> T_Registers_212
du_writeReg_240 v0 v1
  = case coe v1 of
      C_Input_200
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_228 (coe v2) (coe d_output_224 (coe v0))
                  (coe d_stackSlot_226 (coe v0)))
      C_Output_202
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_228 (coe d_input_222 (coe v0)) (coe v2)
                  (coe d_stackSlot_226 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 -> Integer -> T_Registers_212
d_writeStackSlot_252 ~v0 v1 v2 = du_writeStackSlot_252 v1 v2
du_writeStackSlot_252 ::
  T_Registers_212 -> Integer -> T_Registers_212
du_writeStackSlot_252 v0 v1
  = coe
      C_mkRegs_228 (coe d_input_222 (coe v0)) (coe d_output_224 (coe v0))
      (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 -> Integer -> T_Registers_212
d_incrStackSlot_260 ~v0 v1 v2 = du_incrStackSlot_260 v1 v2
du_incrStackSlot_260 ::
  T_Registers_212 -> Integer -> T_Registers_212
du_incrStackSlot_260 v0 v1
  = coe
      C_mkRegs_228 (coe d_input_222 (coe v0)) (coe d_output_224 (coe v0))
      (coe addInt (coe d_stackSlot_226 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 -> Integer -> T_Registers_212
d_decrStackSlot_268 ~v0 v1 v2 = du_decrStackSlot_268 v1 v2
du_decrStackSlot_268 ::
  T_Registers_212 -> Integer -> T_Registers_212
du_decrStackSlot_268 v0 v1
  = coe
      C_mkRegs_228 (coe d_input_222 (coe v0)) (coe d_output_224 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_226 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_288 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_330 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_348 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_368 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_384 a0 = ()
data T_LocState_384
  = C_mkLocState_404 T_Registers_212
                     (AgdaAny -> Integer -> Maybe T_ValueLocation_144)
                     (T_HeapLocation_54 -> Maybe T_HeapLocation_54) Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_396 :: T_LocState_384 -> T_Registers_212
d_regs_396 v0
  = case coe v0 of
      C_mkLocState_404 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_398 ::
  T_LocState_384 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_stackMem_398 v0
  = case coe v0 of
      C_mkLocState_404 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_400 ::
  T_LocState_384 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_heapMem_400 v0
  = case coe v0 of
      C_mkLocState_404 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_402 :: T_LocState_384 -> Bool
d_halted_402 v0
  = case coe v0 of
      C_mkLocState_404 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_406 = ()
data T_AllocMode_406 = C_Stack_408 | C_Heap_410
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_414 a0 = ()
data T_AllocState_414 = C_mkAllocState_478 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_472 :: T_AllocState_414 -> AgdaAny
d_current'45'frame_472 v0
  = case coe v0 of
      C_mkAllocState_478 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_474 :: T_AllocState_414 -> Integer
d_next'45'slot_474 v0
  = case coe v0 of
      C_mkAllocState_478 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_476 :: T_AllocState_414 -> Integer
d_next'45'heap'45'ref_476 v0
  = case coe v0 of
      C_mkAllocState_478 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_508 ::
  T_LocState_384 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_508 v0 v1 v2 = coe d_stackMem_398 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_516 ::
  T_LocState_384 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_516 v0 v1 = coe d_heapMem_400 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_522 ~v0 v1 v2 = du_readLoc_522 v1 v2
du_readLoc_522 ::
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_522 v0 v1
  = case coe v1 of
      C_OnStack_148 v2 v3 -> coe d_stackMem_398 v0 v2 v3
      C_OnHeap_150 v2
        -> let v3 = coe d_heapMem_400 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_OnHeap_150 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_556 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_556 v5 v6 v7 v8
du_writeStackMem'45'aux_556 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_556 v0 v1 v2 v3
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
d_writeStackMem_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_564 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_556
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_578 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_578 v1 v2 v3 v4
du_writeHeapMem_578 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_578 v0 v1 v2 v3
  = let v4
          = coe
              du_'8799'HL'45'aux_74
              (let v4
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         erased
                         (\ v4 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                              (coe d_ref'45'id_24 (coe d_heap'45'ref_60 (coe v1))))
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               eqInt (coe d_ref'45'id_24 (coe d_heap'45'ref_60 (coe v1)))
                               (coe d_ref'45'id_24 (coe d_heap'45'ref_60 (coe v3))))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  eqInt (coe d_ref'45'id_24 (coe d_heap'45'ref_60 (coe v1)))
                                  (coe d_ref'45'id_24 (coe d_heap'45'ref_60 (coe v3)))))) in
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
                 (coe d_heap'45'offset_62 (coe v1))
                 (coe d_heap'45'offset_62 (coe v3))) in
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
d_writeLocToStack_608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_384
d_writeLocToStack_608 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_404 (coe d_regs_396 (coe v1))
      (coe
         d_writeStackMem_564 (coe v0) (coe d_stackMem_398 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_400 (coe v1)) (coe d_halted_402 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
d_writeLocToHeap_618 ~v0 v1 v2 v3 = du_writeLocToHeap_618 v1 v2 v3
du_writeLocToHeap_618 ::
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
du_writeLocToHeap_618 v0 v1 v2
  = coe
      C_mkLocState_404 (coe d_regs_396 (coe v0))
      (coe d_stackMem_398 (coe v0))
      (coe
         du_writeHeapMem_578 (coe d_heapMem_400 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_402 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_384
d_writeLoc_626 v0 v1 v2 v3
  = case coe v2 of
      C_OnStack_148 v4 v5
        -> coe
             d_writeLocToStack_608 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_OnHeap_150 v4
        -> case coe v3 of
             C_OnStack_148 v5 v6 -> coe v1
             C_OnHeap_150 v5
               -> coe du_writeLocToHeap_618 (coe v1) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_652 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_678 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_706 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_706 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_726 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_212 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_726 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_754 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_786 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_882 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_934 a0 = ()
data T_LocSourceExt_934
  = C_Loc_938 T_ValueLocation_144 | C_IndReg_940 T_AbstractReg_198 |
    C_IndRegSuc_942 T_AbstractReg_198
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_212 -> T_LocSourceExt_934 -> T_ValueLocation_144
d_resolveSourceExt_946 ~v0 v1 v2 = du_resolveSourceExt_946 v1 v2
du_resolveSourceExt_946 ::
  T_Registers_212 -> T_LocSourceExt_934 -> T_ValueLocation_144
du_resolveSourceExt_946 v0 v1
  = case coe v1 of
      C_Loc_938 v2 -> coe v2
      C_IndReg_940 v2 -> coe du_readReg_232 (coe v0) (coe v2)
      C_IndRegSuc_942 v2
        -> coe du_sucLoc_168 (coe du_readReg_232 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_962 a0 = ()
data T_Instr_962
  = C_load_966 T_AbstractReg_198 T_LocSourceExt_934 |
    C_store_968 T_LocSourceExt_934 T_AbstractReg_198 |
    C_mov_970 T_AbstractReg_198 T_AbstractReg_198
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_978 ::
  T_LocState_384 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_978 v0 v1 = coe d_heapMem_400 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_980 ~v0 = du_readLoc_980
du_readLoc_980 ::
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_980 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_982 ::
  T_LocState_384 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_982 v0 v1 v2 = coe d_stackMem_398 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_984 ~v0 = du_writeHeapMem_984
du_writeHeapMem_984 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_984 = coe du_writeHeapMem_578
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_384
d_writeLoc_986 v0 = coe d_writeLoc_626 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_988 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_990 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_990 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_992 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_994 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_996 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_998 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1000 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_212 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1000 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
d_writeLocToHeap_1002 ~v0 = du_writeLocToHeap_1002
du_writeLocToHeap_1002 ::
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
du_writeLocToHeap_1002 = coe du_writeLocToHeap_618
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_384
d_writeLocToStack_1004 v0 = coe d_writeLocToStack_608 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1006 v0 = coe d_writeStackMem_564 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1008 ~v0 = du_writeStackMem'45'aux_1008
du_writeStackMem'45'aux_1008 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1008 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_556 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
d_exec'45'load'45'with'45'value_1010 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1010 v1 v2
du_exec'45'load'45'with'45'value_1010 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
du_exec'45'load'45'with'45'value_1010 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_404 (coe du_writeReg_240 (d_regs_396 (coe v3)) v0 v2)
                  (coe d_stackMem_398 (coe v3)) (coe d_heapMem_400 (coe v3))
                  (coe d_halted_402 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_404 (coe d_regs_396 (coe v2))
                  (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_962 -> T_LocState_384 -> T_LocState_384
d_exec_1022 v0 v1
  = case coe v1 of
      C_load_966 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1010 v2
                  (coe
                     du_readLoc_522 (coe v4)
                     (coe du_resolveSourceExt_946 (coe d_regs_396 (coe v4)) (coe v3)))
                  v4)
      C_store_968 v2 v3
        -> coe
             (\ v4 ->
                d_writeLoc_626
                  (coe v0) (coe v4)
                  (coe du_resolveSourceExt_946 (coe d_regs_396 (coe v4)) (coe v2))
                  (coe du_readReg_232 (coe d_regs_396 (coe v4)) (coe v3)))
      C_mov_970 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_404
                  (coe
                     du_writeReg_240 (d_regs_396 (coe v4)) v2
                     (coe du_readReg_232 (coe d_regs_396 (coe v4)) (coe v3)))
                  (coe d_stackMem_398 (coe v4)) (coe d_heapMem_400 (coe v4))
                  (coe d_halted_402 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1052 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1058 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_962] -> T_LocState_384 -> T_LocState_384
d_execList_1060 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_402 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1060 (coe v0) (coe v4) (coe d_exec_1022 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1092 ::
  T_LocState_384 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1092 v0 v1 = coe d_heapMem_400 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_1094 ~v0 = du_readLoc_1094
du_readLoc_1094 ::
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_1094 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1096 ::
  T_LocState_384 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_1096 v0 v1 v2 = coe d_stackMem_398 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1098 ~v0 = du_writeHeapMem_1098
du_writeHeapMem_1098 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1098 = coe du_writeHeapMem_578
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_384
d_writeLoc_1100 v0 = coe d_writeLoc_626 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1102 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1104 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1104 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1106 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1108 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1110 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1112 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1114 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_212 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1114 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
d_writeLocToHeap_1116 ~v0 = du_writeLocToHeap_1116
du_writeLocToHeap_1116 ::
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
du_writeLocToHeap_1116 = coe du_writeLocToHeap_618
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_384
d_writeLocToStack_1118 v0 = coe d_writeLocToStack_608 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1120 v0 = coe d_writeStackMem_564 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1122 ~v0 = du_writeStackMem'45'aux_1122
du_writeStackMem'45'aux_1122 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1122 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_556 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_962 -> T_LocState_384 -> T_LocState_384
d_exec_1126 v0 = coe d_exec_1022 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1128 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1130 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
d_exec'45'load'45'with'45'value_1132 ~v0
  = du_exec'45'load'45'with'45'value_1132
du_exec'45'load'45'with'45'value_1132 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
du_exec'45'load'45'with'45'value_1132
  = coe du_exec'45'load'45'with'45'value_1010
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_962] -> T_LocState_384 -> T_LocState_384
d_execList_1134 v0 = coe d_execList_1060 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1144 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1182 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-preserves
d_load'45'failed'45'preserves_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1224 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1252 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1282 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1312 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 ->
  T_AbstractReg_198 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1328 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1346 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1360 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1376 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1410 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1430 = erased
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1510 = ()
data T_AbstractInstr_1510
  = C_mov'45'to'45'output_1512 | C_mov'45'to'45'input_1514 |
    C_load'45'indirect_1516 | C_load'45'indirect'45'suc_1518 |
    C_load'45'from'45'slot_1520 Integer |
    C_store'45'at'45'slot_1522 Integer | C_store'45'indirect_1524 |
    C_store'45'indirect'45'suc_1526 | C_lea'45'slot_1528 Integer |
    C_restore'45'input_1530 Integer |
    C_instr'45'alloc'45'stack_1532 Integer |
    C_instr'45'dealloc'45'stack_1534 Integer |
    C_instr'45'reclaim'45'to_1536 Integer |
    C_instr'45'push'45'frame_1538 Integer |
    C_instr'45'pop'45'frame_1540 | C_instr'45'call'45'closure_1542 |
    C_worklist'45'init_1544 Integer | C_worklist'45'push_1546 Integer |
    C_worklist'45'pop_1548 Integer | C_worklist'45'check_1550 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1552 :: ()
d_AbstractTrace_1552 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_1554 = ()
data T_TreeTrace_1554
  = C_ε_1556 | C_instr_1558 T_AbstractInstr_1510 |
    C__'9656'__1560 T_TreeTrace_1554 T_TreeTrace_1554 |
    C_branch_1562 Integer T_TreeTrace_1554 T_TreeTrace_1554 |
    C_call'45'sub_1564 T_TreeTrace_1554 |
    C_flat_1566 [T_AbstractInstr_1510]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_1568 :: [T_AbstractInstr_1510] -> T_TreeTrace_1554
d_flatToTree_1568 v0
  = case coe v0 of
      [] -> coe C_ε_1556
      (:) v1 v2
        -> coe
             C__'9656'__1560 (coe C_instr_1558 (coe v1))
             (coe d_flatToTree_1568 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_1574 :: T_TreeTrace_1554 -> [T_AbstractInstr_1510]
d_treeToFlat_1574 v0
  = case coe v0 of
      C_ε_1556 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1558 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1560 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1574 (coe v1)) (coe d_treeToFlat_1574 (coe v2))
      C_branch_1562 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1574 (coe v2)) (coe d_treeToFlat_1574 (coe v3))
      C_call'45'sub_1564 v1 -> coe d_treeToFlat_1574 (coe v1)
      C_flat_1566 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_1590 ::
  Integer -> T_TreeTrace_1554 -> [T_AbstractInstr_1510]
d_treeToRunnable_1590 v0 v1
  = case coe v1 of
      C_ε_1556 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1558 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1560 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1590 (coe v0) (coe v2))
             (coe d_treeToRunnable_1590 (coe v0) (coe v3))
      C_branch_1562 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1590 (coe v0) (coe v3))
             (coe d_treeToRunnable_1590 (coe v0) (coe v4))
      C_call'45'sub_1564 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1546 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_1590 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1548 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_1566 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_1620 ::
  Integer -> T_TreeTrace_1554 -> [T_AbstractInstr_1510]
d_treeToRunnableWithInit_1620 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1544 (coe v0))
      (coe d_treeToRunnable_1590 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_1656 ::
  T_LocState_384 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1656 v0 v1 = coe d_heapMem_400 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_1658 ~v0 = du_readLoc_1658
du_readLoc_1658 ::
  T_LocState_384 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_1658 = coe du_readLoc_522
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_1660 ::
  T_LocState_384 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_1660 v0 v1 v2 = coe d_stackMem_398 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1662 ~v0 = du_writeHeapMem_1662
du_writeHeapMem_1662 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1662 = coe du_writeHeapMem_578
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_384
d_writeLoc_1664 v0 = coe d_writeLoc_626 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1666 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1668 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1668 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1670 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1672 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1674 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1676 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1678 ::
  T_LocState_384 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_212 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1678 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
d_writeLocToHeap_1680 ~v0 = du_writeLocToHeap_1680
du_writeLocToHeap_1680 ::
  T_LocState_384 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_384
du_writeLocToHeap_1680 = coe du_writeLocToHeap_618
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_1682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_384
d_writeLocToStack_1682 v0 = coe d_writeLocToStack_608 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_1684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1684 v0 = coe d_writeStackMem_564 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1686 ~v0 = du_writeStackMem'45'aux_1686
du_writeStackMem'45'aux_1686 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1686 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_556 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_962 -> T_LocState_384 -> T_LocState_384
d_exec_1690 v0 = coe d_exec_1022 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1692 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1694 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_1696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
d_exec'45'load'45'with'45'value_1696 ~v0
  = du_exec'45'load'45'with'45'value_1696
du_exec'45'load'45'with'45'value_1696 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_384 -> T_LocState_384
du_exec'45'load'45'with'45'value_1696
  = coe du_exec'45'load'45'with'45'value_1010
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_1698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_962] -> T_LocState_384 -> T_LocState_384
d_execList_1698 v0 = coe d_execList_1060 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-preserves
d_load'45'failed'45'preserves_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1702 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_1704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1704 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1706 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1708 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1710 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1712 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_934 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1714 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1716 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 ->
  T_AbstractReg_198 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1718 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1720 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_384 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1722 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 ->
  T_LocState_384 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1724 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1726 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1726 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_1726 ::
  Maybe T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1726 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe du_writeReg_240 (d_regs_396 (coe v1)) (coe C_Output_202) v3)
                (coe d_stackMem_398 (coe v1)) (coe d_heapMem_400 (coe v1))
                (coe d_halted_402 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404 (coe d_regs_396 (coe v1))
                (coe d_stackMem_398 (coe v1)) (coe d_heapMem_400 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1738 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_1738 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_1738 ::
  Maybe T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1738 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe du_writeReg_240 (d_regs_396 (coe v1)) (coe C_Input_200) v3)
                (coe d_stackMem_398 (coe v1)) (coe d_heapMem_400 (coe v1))
                (coe d_halted_402 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404 (coe d_regs_396 (coe v1))
                (coe d_stackMem_398 (coe v1)) (coe d_heapMem_400 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1756 ::
  T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1756 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1762 ::
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1762 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1770 ::
  T_ValueLocation_144 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1770 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1776 ::
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1776 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1510 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1778 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1512
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe
                   du_writeReg_240 (d_regs_396 (coe v2)) (coe C_Output_202)
                   (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Input_200)))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1514
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe
                   du_writeReg_240 (d_regs_396 (coe v2)) (coe C_Input_200)
                   (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Output_202)))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe v3)
      C_load'45'indirect_1516
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1010 (coe C_Output_202)
                (coe
                   du_readLoc_522 (coe v2)
                   (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Input_200)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_1518
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1010 (coe C_Output_202)
                (coe
                   du_readLoc_522 (coe v2)
                   (coe
                      du_sucLoc_168
                      (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Input_200))))
                v2)
             (coe v3)
      C_load'45'from'45'slot_1520 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1726
             (coe
                du_readLoc_522 (coe v2)
                (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1522 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_626 (coe v0) (coe v2)
                (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4))
                (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Output_202)))
             (coe v3)
      C_store'45'indirect_1524
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_626 (coe v0) (coe v2)
                (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Input_200))
                (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Output_202)))
             (coe v3)
      C_store'45'indirect'45'suc_1526
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_626 (coe v0) (coe v2)
                (coe
                   du_sucLoc_168
                   (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Input_200)))
                (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Output_202)))
             (coe v3)
      C_lea'45'slot_1528 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe
                   du_writeReg_240 (d_regs_396 (coe v2)) (coe C_Output_202)
                   (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4)))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe v3)
      C_restore'45'input_1530 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_1738
             (coe
                du_readLoc_522 (coe v2)
                (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1532 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe du_incrStackSlot_260 (coe d_regs_396 (coe v2)) (coe v4))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe
                C_mkAllocState_478 (coe d_current'45'frame_472 (coe v3))
                (coe addInt (coe d_next'45'slot_474 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_476 (coe v3)))
      C_instr'45'dealloc'45'stack_1534 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe du_decrStackSlot_268 (coe d_regs_396 (coe v2)) (coe v4))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1536 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_478 (coe d_current'45'frame_472 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_476 (coe v3)))
      C_instr'45'push'45'frame_1538 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_404
                (coe
                   du_writeStackSlot_252 (coe d_regs_396 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_398 (coe v2)) (coe d_heapMem_400 (coe v2))
                (coe d_halted_402 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1540
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1542
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1544 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1546 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_626 (coe v0) (coe v2)
                (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4))
                (coe du_readReg_232 (coe d_regs_396 (coe v2)) (coe C_Output_202)))
             (coe v3)
      C_worklist'45'pop_1548 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1726
             (coe
                du_readLoc_522 (coe v2)
                (coe C_OnStack_148 (coe d_current'45'frame_472 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1550 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1510] ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_1884 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_402 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_1884 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_1778 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_1778 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1510 ->
  [T_AbstractInstr_1510] ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_1934 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_1980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1510 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_1980 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_384 -> T_AllocState_414 -> Integer -> Maybe Integer
d_getTag_2014 ~v0 v1 v2 v3 = du_getTag_2014 v1 v2 v3
du_getTag_2014 ::
  T_LocState_384 -> T_AllocState_414 -> Integer -> Maybe Integer
du_getTag_2014 v0 v1 v2
  = let v3
          = coe d_stackMem_398 v0 (d_current'45'frame_472 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1554 ->
  T_LocState_384 ->
  T_AllocState_414 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2038 v0 v1 v2 v3
  = case coe v1 of
      C_ε_1556
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_1558 v4
        -> let v5 = d_halted_402 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_1778 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__1560 v4 v5
        -> let v6 = d_halted_402 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2038 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2038 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2038 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_1562 v4 v5 v6
        -> let v7 = d_halted_402 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_398 v2 (d_current'45'frame_472 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2038 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2038 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2038 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2038 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2038 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_1564 v4
        -> let v5 = d_halted_402 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2038 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_1566 v4
        -> coe d_exec'45'trace_1884 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2198 ::
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2198 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1554 ->
  T_TreeTrace_1554 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2216 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1510 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2262 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1554 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2302 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1510] ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2342 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1510] ->
  [T_AbstractInstr_1510] ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2362 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2420
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1554 ->
  T_LocState_384 ->
  T_AllocState_414 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2428 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2428
du_exec'45'tree'45'flat'45'equiv'45'simple_2428 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2428
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
