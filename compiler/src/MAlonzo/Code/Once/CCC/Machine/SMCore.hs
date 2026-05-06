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
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Type
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
  = C_AtStack_148 AgdaAny Integer | C_AtDynamic_150 T_HeapLocation_54
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
      C_AtStack_148 v1 v2
        -> coe
             C_AtStack_148 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_AtDynamic_150 v1
        -> coe C_AtDynamic_150 (coe d_sucHL_152 (coe v1))
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
      C_AtStack_148 v2 v3
        -> coe C_AtStack_148 (coe v2) (coe addInt (coe v1) (coe v3))
      C_AtDynamic_150 v2
        -> coe C_AtDynamic_150 (coe d_offsetHL_158 (coe v2) (coe v1))
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
data T_AbstractReg_198 = C_Input1_200 | C_Input2_202 | C_Output_204
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__210 ::
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__210 v0 v1
  = case coe v0 of
      C_Input1_200
        -> case coe v1 of
             C_Input1_200
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Input2_202
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_204
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Input2_202
        -> case coe v1 of
             C_Input1_200
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_202
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_204
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_204
        -> case coe v1 of
             C_Input1_200
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_202
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_204
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_214 a0 = ()
data T_Registers_214
  = C_mkRegs_234 T_ValueLocation_144 T_ValueLocation_144
                 T_ValueLocation_144 Integer
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_226 :: T_Registers_214 -> T_ValueLocation_144
d_input1_226 v0
  = case coe v0 of
      C_mkRegs_234 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_228 :: T_Registers_214 -> T_ValueLocation_144
d_input2_228 v0
  = case coe v0 of
      C_mkRegs_234 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_230 :: T_Registers_214 -> T_ValueLocation_144
d_output_230 v0
  = case coe v0 of
      C_mkRegs_234 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_232 :: T_Registers_214 -> Integer
d_stackSlot_232 v0
  = case coe v0 of
      C_mkRegs_234 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 -> T_AbstractReg_198 -> T_ValueLocation_144
d_readReg_238 ~v0 v1 v2 = du_readReg_238 v1 v2
du_readReg_238 ::
  T_Registers_214 -> T_AbstractReg_198 -> T_ValueLocation_144
du_readReg_238 v0 v1
  = case coe v1 of
      C_Input1_200 -> coe d_input1_226 (coe v0)
      C_Input2_202 -> coe d_input2_228 (coe v0)
      C_Output_204 -> coe d_output_230 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 ->
  T_AbstractReg_198 -> T_ValueLocation_144 -> T_Registers_214
d_writeReg_248 ~v0 v1 v2 = du_writeReg_248 v1 v2
du_writeReg_248 ::
  T_Registers_214 ->
  T_AbstractReg_198 -> T_ValueLocation_144 -> T_Registers_214
du_writeReg_248 v0 v1
  = case coe v1 of
      C_Input1_200
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_234 (coe v2) (coe d_input2_228 (coe v0))
                  (coe d_output_230 (coe v0)) (coe d_stackSlot_232 (coe v0)))
      C_Input2_202
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_234 (coe d_input1_226 (coe v0)) (coe v2)
                  (coe d_output_230 (coe v0)) (coe d_stackSlot_232 (coe v0)))
      C_Output_204
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_234 (coe d_input1_226 (coe v0))
                  (coe d_input2_228 (coe v0)) (coe v2)
                  (coe d_stackSlot_232 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 -> Integer -> T_Registers_214
d_writeStackSlot_264 ~v0 v1 v2 = du_writeStackSlot_264 v1 v2
du_writeStackSlot_264 ::
  T_Registers_214 -> Integer -> T_Registers_214
du_writeStackSlot_264 v0 v1
  = coe
      C_mkRegs_234 (coe d_input1_226 (coe v0))
      (coe d_input2_228 (coe v0)) (coe d_output_230 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 -> Integer -> T_Registers_214
d_incrStackSlot_272 ~v0 v1 v2 = du_incrStackSlot_272 v1 v2
du_incrStackSlot_272 ::
  T_Registers_214 -> Integer -> T_Registers_214
du_incrStackSlot_272 v0 v1
  = coe
      C_mkRegs_234 (coe d_input1_226 (coe v0))
      (coe d_input2_228 (coe v0)) (coe d_output_230 (coe v0))
      (coe addInt (coe d_stackSlot_232 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 -> Integer -> T_Registers_214
d_decrStackSlot_280 ~v0 v1 v2 = du_decrStackSlot_280 v1 v2
du_decrStackSlot_280 ::
  T_Registers_214 -> Integer -> T_Registers_214
du_decrStackSlot_280 v0 v1
  = coe
      C_mkRegs_234 (coe d_input1_226 (coe v0))
      (coe d_input2_228 (coe v0)) (coe d_output_230 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_232 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_300 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_376 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_398 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_422 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_444 a0 = ()
data T_LocState_444
  = C_mkLocState_464 T_Registers_214
                     (AgdaAny -> Integer -> Maybe T_ValueLocation_144)
                     (T_HeapLocation_54 -> Maybe T_HeapLocation_54) Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_456 :: T_LocState_444 -> T_Registers_214
d_regs_456 v0
  = case coe v0 of
      C_mkLocState_464 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_458 ::
  T_LocState_444 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_stackMem_458 v0
  = case coe v0 of
      C_mkLocState_464 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_460 ::
  T_LocState_444 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_heapMem_460 v0
  = case coe v0 of
      C_mkLocState_464 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_462 :: T_LocState_444 -> Bool
d_halted_462 v0
  = case coe v0 of
      C_mkLocState_464 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_466 = ()
data T_AllocMode_466 = C_Stack_468 | C_Heap_470
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_474 a0 = ()
data T_AllocState_474 = C_mkAllocState_538 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_532 :: T_AllocState_474 -> AgdaAny
d_current'45'frame_532 v0
  = case coe v0 of
      C_mkAllocState_538 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_534 :: T_AllocState_474 -> Integer
d_next'45'slot_534 v0
  = case coe v0 of
      C_mkAllocState_538 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_536 :: T_AllocState_474 -> Integer
d_next'45'heap'45'ref_536 v0
  = case coe v0 of
      C_mkAllocState_538 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_568 ::
  T_LocState_444 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_568 v0 v1 v2 = coe d_stackMem_458 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_576 ::
  T_LocState_444 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_576 v0 v1 = coe d_heapMem_460 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_582 ~v0 v1 v2 = du_readLoc_582 v1 v2
du_readLoc_582 ::
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_582 v0 v1
  = case coe v1 of
      C_AtStack_148 v2 v3 -> coe d_stackMem_458 v0 v2 v3
      C_AtDynamic_150 v2
        -> let v3 = coe d_heapMem_460 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_AtDynamic_150 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_616 v5 v6 v7 v8
du_writeStackMem'45'aux_616 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_616 v0 v1 v2 v3
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
d_writeStackMem_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_624 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_616
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_638 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_638 v1 v2 v3 v4
du_writeHeapMem_638 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_638 v0 v1 v2 v3
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
d_writeLocToStack_668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_444
d_writeLocToStack_668 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_464 (coe d_regs_456 (coe v1))
      (coe
         d_writeStackMem_624 (coe v0) (coe d_stackMem_458 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_460 (coe v1)) (coe d_halted_462 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
d_writeLocToHeap_678 ~v0 v1 v2 v3 = du_writeLocToHeap_678 v1 v2 v3
du_writeLocToHeap_678 ::
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
du_writeLocToHeap_678 v0 v1 v2
  = coe
      C_mkLocState_464 (coe d_regs_456 (coe v0))
      (coe d_stackMem_458 (coe v0))
      (coe
         du_writeHeapMem_638 (coe d_heapMem_460 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_462 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_444
d_writeLoc_686 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_148 v4 v5
        -> coe
             d_writeLocToStack_668 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_150 v4
        -> case coe v3 of
             C_AtStack_148 v5 v6 -> coe v1
             C_AtDynamic_150 v5
               -> coe du_writeLocToHeap_678 (coe v1) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_712 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_738 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_766 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_766 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_786 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_786 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_814 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_846 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_942 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_994 a0 = ()
data T_LocSourceExt_994
  = C_Loc_998 T_ValueLocation_144 | C_IndReg_1000 T_AbstractReg_198 |
    C_IndRegSuc_1002 T_AbstractReg_198
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_214 -> T_LocSourceExt_994 -> T_ValueLocation_144
d_resolveSourceExt_1006 ~v0 v1 v2 = du_resolveSourceExt_1006 v1 v2
du_resolveSourceExt_1006 ::
  T_Registers_214 -> T_LocSourceExt_994 -> T_ValueLocation_144
du_resolveSourceExt_1006 v0 v1
  = case coe v1 of
      C_Loc_998 v2 -> coe v2
      C_IndReg_1000 v2 -> coe du_readReg_238 (coe v0) (coe v2)
      C_IndRegSuc_1002 v2
        -> coe du_sucLoc_168 (coe du_readReg_238 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1022 a0 = ()
data T_Instr_1022
  = C_load_1026 T_AbstractReg_198 T_LocSourceExt_994 |
    C_store_1028 T_LocSourceExt_994 T_AbstractReg_198 |
    C_mov_1030 T_AbstractReg_198 T_AbstractReg_198
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1038 ::
  T_LocState_444 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1038 v0 v1 = coe d_heapMem_460 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_1040 ~v0 = du_readLoc_1040
du_readLoc_1040 ::
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_1040 = coe du_readLoc_582
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1042 ::
  T_LocState_444 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_1042 v0 v1 v2 = coe d_stackMem_458 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1044 ~v0 = du_writeHeapMem_1044
du_writeHeapMem_1044 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1044 = coe du_writeHeapMem_638
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_444
d_writeLoc_1046 v0 = coe d_writeLoc_686 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1048 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1050 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1050 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1052 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1054 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1056 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1058 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1060 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1060 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
d_writeLocToHeap_1062 ~v0 = du_writeLocToHeap_1062
du_writeLocToHeap_1062 ::
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
du_writeLocToHeap_1062 = coe du_writeLocToHeap_678
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_444
d_writeLocToStack_1064 v0 = coe d_writeLocToStack_668 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1066 v0 = coe d_writeStackMem_624 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1068 ~v0 = du_writeStackMem'45'aux_1068
du_writeStackMem'45'aux_1068 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1068 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_616 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
d_exec'45'load'45'with'45'value_1070 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1070 v1 v2
du_exec'45'load'45'with'45'value_1070 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
du_exec'45'load'45'with'45'value_1070 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_464 (coe du_writeReg_248 (d_regs_456 (coe v3)) v0 v2)
                  (coe d_stackMem_458 (coe v3)) (coe d_heapMem_460 (coe v3))
                  (coe d_halted_462 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_464 (coe d_regs_456 (coe v2))
                  (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1022 -> T_LocState_444 -> T_LocState_444
d_exec_1082 v0 v1
  = case coe v1 of
      C_load_1026 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1070 v2
                  (coe
                     du_readLoc_582 (coe v4)
                     (coe du_resolveSourceExt_1006 (coe d_regs_456 (coe v4)) (coe v3)))
                  v4)
      C_store_1028 v2 v3
        -> coe
             (\ v4 ->
                d_writeLoc_686
                  (coe v0) (coe v4)
                  (coe du_resolveSourceExt_1006 (coe d_regs_456 (coe v4)) (coe v2))
                  (coe du_readReg_238 (coe d_regs_456 (coe v4)) (coe v3)))
      C_mov_1030 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_464
                  (coe
                     du_writeReg_248 (d_regs_456 (coe v4)) v2
                     (coe du_readReg_238 (coe d_regs_456 (coe v4)) (coe v3)))
                  (coe d_stackMem_458 (coe v4)) (coe d_heapMem_460 (coe v4))
                  (coe d_halted_462 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1112 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1118 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1022] -> T_LocState_444 -> T_LocState_444
d_execList_1120 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_462 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1120 (coe v0) (coe v4) (coe d_exec_1082 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1152 ::
  T_LocState_444 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1152 v0 v1 = coe d_heapMem_460 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_1154 ~v0 = du_readLoc_1154
du_readLoc_1154 ::
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_1154 = coe du_readLoc_582
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1156 ::
  T_LocState_444 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_1156 v0 v1 v2 = coe d_stackMem_458 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1158 ~v0 = du_writeHeapMem_1158
du_writeHeapMem_1158 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1158 = coe du_writeHeapMem_638
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_444
d_writeLoc_1160 v0 = coe d_writeLoc_686 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1162 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1164 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1164 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1166 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1168 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1170 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1172 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1174 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1174 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
d_writeLocToHeap_1176 ~v0 = du_writeLocToHeap_1176
du_writeLocToHeap_1176 ::
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
du_writeLocToHeap_1176 = coe du_writeLocToHeap_678
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_444
d_writeLocToStack_1178 v0 = coe d_writeLocToStack_668 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1180 v0 = coe d_writeStackMem_624 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1182 ~v0 = du_writeStackMem'45'aux_1182
du_writeStackMem'45'aux_1182 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1182 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_616 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1022 -> T_LocState_444 -> T_LocState_444
d_exec_1186 v0 = coe d_exec_1082 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1188 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1190 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
d_exec'45'load'45'with'45'value_1192 ~v0
  = du_exec'45'load'45'with'45'value_1192
du_exec'45'load'45'with'45'value_1192 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
du_exec'45'load'45'with'45'value_1192
  = coe du_exec'45'load'45'with'45'value_1070
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1022] -> T_LocState_444 -> T_LocState_444
d_execList_1194 v0 = coe d_execList_1120 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1204 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1242 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-preserves
d_load'45'failed'45'preserves_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1284 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1312 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1342 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1372 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 ->
  T_AbstractReg_198 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1388 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1406 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1420 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1436 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1470 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1490 = erased
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1570 = ()
data T_AbstractInstr_1570
  = C_mov'45'to'45'output_1572 | C_mov'45'to'45'input_1574 |
    C_mov'45'output'45'to'45'input2_1576 |
    C_mov'45'input2'45'to'45'output_1578 | C_load'45'indirect_1580 |
    C_load'45'indirect'45'suc_1582 |
    C_load'45'from'45'slot_1584 Integer |
    C_store'45'at'45'slot_1586 Integer | C_store'45'indirect_1588 |
    C_store'45'indirect'45'suc_1590 | C_lea'45'slot_1592 Integer |
    C_restore'45'input_1594 Integer |
    C_instr'45'alloc'45'stack_1596 Integer |
    C_instr'45'dealloc'45'stack_1598 Integer |
    C_instr'45'reclaim'45'to_1600 Integer |
    C_instr'45'push'45'frame_1602 Integer |
    C_instr'45'pop'45'frame_1604 | C_instr'45'call'45'closure_1606 |
    C_worklist'45'init_1608 Integer | C_worklist'45'push_1610 Integer |
    C_worklist'45'pop_1612 Integer | C_worklist'45'check_1614 Integer |
    C_instr'45'sigop_1620 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_264 |
    C_instr'45'load'45'const_1624 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_IsPrimitive_188 AgdaAny |
    C_instr'45'load'45'code'45'addr_1626 Integer |
    C_instr'45'save'45'closure'45'reg_1628
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1630 :: ()
d_AbstractTrace_1630 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_1632 = ()
data T_TreeTrace_1632
  = C_ε_1634 | C_instr_1636 T_AbstractInstr_1570 |
    C__'9656'__1638 T_TreeTrace_1632 T_TreeTrace_1632 |
    C_branch_1640 Integer T_TreeTrace_1632 T_TreeTrace_1632 |
    C_call'45'sub_1642 T_TreeTrace_1632 |
    C_flat_1644 [T_AbstractInstr_1570]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_1646 :: [T_AbstractInstr_1570] -> T_TreeTrace_1632
d_flatToTree_1646 v0
  = case coe v0 of
      [] -> coe C_ε_1634
      (:) v1 v2
        -> coe
             C__'9656'__1638 (coe C_instr_1636 (coe v1))
             (coe d_flatToTree_1646 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_1652 :: T_TreeTrace_1632 -> [T_AbstractInstr_1570]
d_treeToFlat_1652 v0
  = case coe v0 of
      C_ε_1634 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1636 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1638 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1652 (coe v1)) (coe d_treeToFlat_1652 (coe v2))
      C_branch_1640 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1652 (coe v2)) (coe d_treeToFlat_1652 (coe v3))
      C_call'45'sub_1642 v1 -> coe d_treeToFlat_1652 (coe v1)
      C_flat_1644 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_1668 ::
  Integer -> T_TreeTrace_1632 -> [T_AbstractInstr_1570]
d_treeToRunnable_1668 v0 v1
  = case coe v1 of
      C_ε_1634 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1636 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1638 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1668 (coe v0) (coe v2))
             (coe d_treeToRunnable_1668 (coe v0) (coe v3))
      C_branch_1640 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1668 (coe v0) (coe v3))
             (coe d_treeToRunnable_1668 (coe v0) (coe v4))
      C_call'45'sub_1642 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1610 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_1668 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1612 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_1644 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_1698 ::
  Integer -> T_TreeTrace_1632 -> [T_AbstractInstr_1570]
d_treeToRunnableWithInit_1698 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1608 (coe v0))
      (coe d_treeToRunnable_1668 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_1734 ::
  T_LocState_444 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1734 v0 v1 = coe d_heapMem_460 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_readLoc_1736 ~v0 = du_readLoc_1736
du_readLoc_1736 ::
  T_LocState_444 -> T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_readLoc_1736 = coe du_readLoc_582
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_1738 ::
  T_LocState_444 -> AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_readStackLoc_1738 v0 v1 v2 = coe d_stackMem_458 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1740 ~v0 = du_writeHeapMem_1740
du_writeHeapMem_1740 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1740 = coe du_writeHeapMem_638
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 -> T_ValueLocation_144 -> T_LocState_444
d_writeLoc_1742 v0 = coe d_writeLoc_686 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_1744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1744 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1746 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1746 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1748 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1750 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1752 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_1754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1754 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1756 ::
  T_LocState_444 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  T_Registers_214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1756 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_1758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
d_writeLocToHeap_1758 ~v0 = du_writeLocToHeap_1758
du_writeLocToHeap_1758 ::
  T_LocState_444 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_444
du_writeLocToHeap_1758 = coe du_writeLocToHeap_678
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_1760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  AgdaAny -> Integer -> T_ValueLocation_144 -> T_LocState_444
d_writeLocToStack_1760 v0 = coe d_writeLocToStack_668 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_144) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_144 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_144
d_writeStackMem_1762 v0 = coe d_writeStackMem_624 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
d_writeStackMem'45'aux_1764 ~v0 = du_writeStackMem'45'aux_1764
du_writeStackMem'45'aux_1764 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_144 ->
  T_ValueLocation_144 -> Maybe T_ValueLocation_144
du_writeStackMem'45'aux_1764 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_616 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_1768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1022 -> T_LocState_444 -> T_LocState_444
d_exec_1768 v0 = coe d_exec_1082 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_1770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1770 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1772 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_1774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
d_exec'45'load'45'with'45'value_1774 ~v0
  = du_exec'45'load'45'with'45'value_1774
du_exec'45'load'45'with'45'value_1774 ::
  T_AbstractReg_198 ->
  Maybe T_ValueLocation_144 -> T_LocState_444 -> T_LocState_444
du_exec'45'load'45'with'45'value_1774
  = coe du_exec'45'load'45'with'45'value_1070
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_1776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1022] -> T_LocState_444 -> T_LocState_444
d_execList_1776 v0 = coe d_execList_1120 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-preserves
d_load'45'failed'45'preserves_1780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1780 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_1782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1782 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_1784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1784 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1786 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_AbstractReg_198 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1788 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1790 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_1792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_LocSourceExt_994 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1792 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1794 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_1796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 ->
  T_AbstractReg_198 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1796 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1798 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_1800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_198 ->
  T_AbstractReg_198 ->
  T_LocState_444 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1800 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 ->
  T_LocState_444 ->
  T_ValueLocation_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1802 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1804 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1804 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_1804 ::
  Maybe T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1804 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe du_writeReg_248 (d_regs_456 (coe v1)) (coe C_Output_204) v3)
                (coe d_stackMem_458 (coe v1)) (coe d_heapMem_460 (coe v1))
                (coe d_halted_462 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464 (coe d_regs_456 (coe v1))
                (coe d_stackMem_458 (coe v1)) (coe d_heapMem_460 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1816 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_1816 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_1816 ::
  Maybe T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1816 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe du_writeReg_248 (d_regs_456 (coe v1)) (coe C_Input1_200) v3)
                (coe d_stackMem_458 (coe v1)) (coe d_heapMem_460 (coe v1))
                (coe d_halted_462 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464 (coe d_regs_456 (coe v1))
                (coe d_stackMem_458 (coe v1)) (coe d_heapMem_460 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1834 ::
  T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1834 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1840 ::
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1840 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1848 ::
  T_ValueLocation_144 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1848 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1854 ::
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1854 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_1860
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_1866
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts"
-- Once.CCC.Machine.SMCore.AbstractExec.encode-const
d_encode'45'const_1870
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.encode-const"
-- Once.CCC.Machine.SMCore.AbstractExec.encode-code-addr
d_encode'45'code'45'addr_1872
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.encode-code-addr"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_1874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1570 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1874 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1572
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input1_200)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1574
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Input1_200)
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_1576
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Input2_202)
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_1578
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input2_202)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_load'45'indirect_1580
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1070 (coe C_Output_204)
                (coe
                   du_readLoc_582 (coe v2)
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input1_200)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_1582
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1070 (coe C_Output_204)
                (coe
                   du_readLoc_582 (coe v2)
                   (coe
                      du_sucLoc_168
                      (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input1_200))))
                v2)
             (coe v3)
      C_load'45'from'45'slot_1584 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1804
             (coe
                du_readLoc_582 (coe v2)
                (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1586 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_686 (coe v0) (coe v2)
                (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4))
                (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
             (coe v3)
      C_store'45'indirect_1588
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_686 (coe v0) (coe v2)
                (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input1_200))
                (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
             (coe v3)
      C_store'45'indirect'45'suc_1590
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_686 (coe v0) (coe v2)
                (coe
                   du_sucLoc_168
                   (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Input1_200)))
                (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
             (coe v3)
      C_lea'45'slot_1592 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_restore'45'input_1594 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_1816
             (coe
                du_readLoc_582 (coe v2)
                (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1596 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe du_incrStackSlot_272 (coe d_regs_456 (coe v2)) (coe v4))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe
                C_mkAllocState_538 (coe d_current'45'frame_532 (coe v3))
                (coe addInt (coe d_next'45'slot_534 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_536 (coe v3)))
      C_instr'45'dealloc'45'stack_1598 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe du_decrStackSlot_280 (coe d_regs_456 (coe v2)) (coe v4))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1600 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_538 (coe d_current'45'frame_532 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_536 (coe v3)))
      C_instr'45'push'45'frame_1602 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeStackSlot_264 (coe d_regs_456 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1604
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1606
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1608 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1610 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_686 (coe v0) (coe v2)
                (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4))
                (coe du_readReg_238 (coe d_regs_456 (coe v2)) (coe C_Output_204)))
             (coe v3)
      C_worklist'45'pop_1612 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1804
             (coe
                du_readLoc_582 (coe v2)
                (coe C_AtStack_148 (coe d_current'45'frame_532 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1614 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_1620 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe d_exec'45'sigop'45'output_1860 v0 v4 v5 v6 v2))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_exec'45'sigop'45'halts_1866 v0 v4 v5 v6 v2))
             (coe v3)
      C_instr'45'load'45'const_1624 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe d_encode'45'const_1870 v0 v4 v5 v6))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_1626 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_464
                (coe
                   du_writeReg_248 (d_regs_456 (coe v2)) (coe C_Output_204)
                   (coe d_encode'45'code'45'addr_1872 v0 v4))
                (coe d_stackMem_458 (coe v2)) (coe d_heapMem_460 (coe v2))
                (coe d_halted_462 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_1628
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1570] ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2012 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_462 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2012 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_1874 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_1874 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1570 ->
  [T_AbstractInstr_1570] ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2062 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1570 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2108 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_444 -> T_AllocState_474 -> Integer -> Maybe Integer
d_getTag_2142 ~v0 v1 v2 v3 = du_getTag_2142 v1 v2 v3
du_getTag_2142 ::
  T_LocState_444 -> T_AllocState_474 -> Integer -> Maybe Integer
du_getTag_2142 v0 v1 v2
  = let v3
          = coe d_stackMem_458 v0 (d_current'45'frame_532 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1632 ->
  T_LocState_444 ->
  T_AllocState_474 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2166 v0 v1 v2 v3
  = case coe v1 of
      C_ε_1634
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_1636 v4
        -> let v5 = d_halted_462 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_1874 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__1638 v4 v5
        -> let v6 = d_halted_462 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2166 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2166 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2166 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_1640 v4 v5 v6
        -> let v7 = d_halted_462 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_458 v2 (d_current'45'frame_532 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2166 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2166 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2166 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2166 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2166 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_1642 v4
        -> let v5 = d_halted_462 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2166 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_1644 v4
        -> coe d_exec'45'trace_2012 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2326 ::
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2326 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1632 ->
  T_TreeTrace_1632 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2344 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1570 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2390 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1632 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2430 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1570] ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2470 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1570] ->
  [T_AbstractInstr_1570] ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2490 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2548
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1632 ->
  T_LocState_444 ->
  T_AllocState_474 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2556 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2556
du_exec'45'tree'45'flat'45'equiv'45'simple_2556 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2556
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
