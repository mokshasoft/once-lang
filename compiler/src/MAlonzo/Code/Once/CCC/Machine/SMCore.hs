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
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_142 = ()
data T_AbstractReg_142 = C_Input1_144 | C_Input2_146 | C_Output_148
-- Once.CCC.Machine.SMCore.ValueLocation
d_ValueLocation_152 a0 = ()
data T_ValueLocation_152
  = C_AtStack_156 AgdaAny Integer |
    C_AtDynamic_158 T_HeapLocation_54 | C_InReg_160 T_AbstractReg_142
-- Once.CCC.Machine.SMCore.sucHL
d_sucHL_162 :: T_HeapLocation_54 -> T_HeapLocation_54
d_sucHL_162 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2
        -> coe
             C_heap'45'loc_64 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetHL
d_offsetHL_168 :: T_HeapLocation_54 -> Integer -> T_HeapLocation_54
d_offsetHL_168 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> coe C_heap'45'loc_64 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_152 -> T_ValueLocation_152
d_sucLoc_178 ~v0 v1 = du_sucLoc_178 v1
du_sucLoc_178 :: T_ValueLocation_152 -> T_ValueLocation_152
du_sucLoc_178 v0
  = case coe v0 of
      C_AtStack_156 v1 v2
        -> coe
             C_AtStack_156 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_AtDynamic_158 v1
        -> coe C_AtDynamic_158 (coe d_sucHL_162 (coe v1))
      C_InReg_160 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_152 -> Integer -> T_ValueLocation_152
d_offsetLoc_190 ~v0 v1 v2 = du_offsetLoc_190 v1 v2
du_offsetLoc_190 ::
  T_ValueLocation_152 -> Integer -> T_ValueLocation_152
du_offsetLoc_190 v0 v1
  = case coe v0 of
      C_AtStack_156 v2 v3
        -> coe C_AtStack_156 (coe v2) (coe addInt (coe v1) (coe v3))
      C_AtDynamic_158 v2
        -> coe C_AtDynamic_158 (coe d_offsetHL_168 (coe v2) (coe v1))
      C_InReg_160 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_206 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_210 :: ()
d_HeapMem_210 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__216 ::
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__216 v0 v1
  = case coe v0 of
      C_Input1_144
        -> case coe v1 of
             C_Input1_144
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Input2_146
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_148
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Input2_146
        -> case coe v1 of
             C_Input1_144
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_146
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_148
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_148
        -> case coe v1 of
             C_Input1_144
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_146
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_148
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_220 a0 = ()
data T_Registers_220
  = C_mkRegs_240 T_ValueLocation_152 T_ValueLocation_152
                 T_ValueLocation_152 Integer
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_232 :: T_Registers_220 -> T_ValueLocation_152
d_input1_232 v0
  = case coe v0 of
      C_mkRegs_240 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_234 :: T_Registers_220 -> T_ValueLocation_152
d_input2_234 v0
  = case coe v0 of
      C_mkRegs_240 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_236 :: T_Registers_220 -> T_ValueLocation_152
d_output_236 v0
  = case coe v0 of
      C_mkRegs_240 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_238 :: T_Registers_220 -> Integer
d_stackSlot_238 v0
  = case coe v0 of
      C_mkRegs_240 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 -> T_AbstractReg_142 -> T_ValueLocation_152
d_readReg_244 ~v0 v1 v2 = du_readReg_244 v1 v2
du_readReg_244 ::
  T_Registers_220 -> T_AbstractReg_142 -> T_ValueLocation_152
du_readReg_244 v0 v1
  = case coe v1 of
      C_Input1_144 -> coe d_input1_232 (coe v0)
      C_Input2_146 -> coe d_input2_234 (coe v0)
      C_Output_148 -> coe d_output_236 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 ->
  T_AbstractReg_142 -> T_ValueLocation_152 -> T_Registers_220
d_writeReg_254 ~v0 v1 v2 = du_writeReg_254 v1 v2
du_writeReg_254 ::
  T_Registers_220 ->
  T_AbstractReg_142 -> T_ValueLocation_152 -> T_Registers_220
du_writeReg_254 v0 v1
  = case coe v1 of
      C_Input1_144
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_240 (coe v2) (coe d_input2_234 (coe v0))
                  (coe d_output_236 (coe v0)) (coe d_stackSlot_238 (coe v0)))
      C_Input2_146
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_240 (coe d_input1_232 (coe v0)) (coe v2)
                  (coe d_output_236 (coe v0)) (coe d_stackSlot_238 (coe v0)))
      C_Output_148
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_240 (coe d_input1_232 (coe v0))
                  (coe d_input2_234 (coe v0)) (coe v2)
                  (coe d_stackSlot_238 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 -> Integer -> T_Registers_220
d_writeStackSlot_270 ~v0 v1 v2 = du_writeStackSlot_270 v1 v2
du_writeStackSlot_270 ::
  T_Registers_220 -> Integer -> T_Registers_220
du_writeStackSlot_270 v0 v1
  = coe
      C_mkRegs_240 (coe d_input1_232 (coe v0))
      (coe d_input2_234 (coe v0)) (coe d_output_236 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 -> Integer -> T_Registers_220
d_incrStackSlot_278 ~v0 v1 v2 = du_incrStackSlot_278 v1 v2
du_incrStackSlot_278 ::
  T_Registers_220 -> Integer -> T_Registers_220
du_incrStackSlot_278 v0 v1
  = coe
      C_mkRegs_240 (coe d_input1_232 (coe v0))
      (coe d_input2_234 (coe v0)) (coe d_output_236 (coe v0))
      (coe addInt (coe d_stackSlot_238 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 -> Integer -> T_Registers_220
d_decrStackSlot_286 ~v0 v1 v2 = du_decrStackSlot_286 v1 v2
du_decrStackSlot_286 ::
  T_Registers_220 -> Integer -> T_Registers_220
du_decrStackSlot_286 v0 v1
  = coe
      C_mkRegs_240 (coe d_input1_232 (coe v0))
      (coe d_input2_234 (coe v0)) (coe d_output_236 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_238 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_306 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_382 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_404 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_428 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_450 a0 = ()
data T_LocState_450
  = C_mkLocState_470 T_Registers_220
                     (AgdaAny -> Integer -> Maybe T_ValueLocation_152)
                     (T_HeapLocation_54 -> Maybe T_HeapLocation_54) Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_462 :: T_LocState_450 -> T_Registers_220
d_regs_462 v0
  = case coe v0 of
      C_mkLocState_470 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_464 ::
  T_LocState_450 -> AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_stackMem_464 v0
  = case coe v0 of
      C_mkLocState_470 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_466 ::
  T_LocState_450 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_heapMem_466 v0
  = case coe v0 of
      C_mkLocState_470 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_468 :: T_LocState_450 -> Bool
d_halted_468 v0
  = case coe v0 of
      C_mkLocState_470 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_472 = ()
data T_AllocMode_472 = C_Stack_474 | C_Heap_476
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_480 a0 = ()
data T_AllocState_480 = C_mkAllocState_544 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_538 :: T_AllocState_480 -> AgdaAny
d_current'45'frame_538 v0
  = case coe v0 of
      C_mkAllocState_544 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_540 :: T_AllocState_480 -> Integer
d_next'45'slot_540 v0
  = case coe v0 of
      C_mkAllocState_544 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_542 :: T_AllocState_480 -> Integer
d_next'45'heap'45'ref_542 v0
  = case coe v0 of
      C_mkAllocState_544 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_574 ::
  T_LocState_450 -> AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_readStackLoc_574 v0 v1 v2 = coe d_stackMem_464 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_582 ::
  T_LocState_450 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_582 v0 v1 = coe d_heapMem_466 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_readLoc_588 ~v0 v1 v2 = du_readLoc_588 v1 v2
du_readLoc_588 ::
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_readLoc_588 v0 v1
  = case coe v1 of
      C_AtStack_156 v2 v3 -> coe d_stackMem_464 v0 v2 v3
      C_AtDynamic_158 v2
        -> let v3 = coe d_heapMem_466 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_AtDynamic_158 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_InReg_160 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_readReg_244 (coe d_regs_462 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_writeStackMem'45'aux_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_626 v5 v6 v7 v8
du_writeStackMem'45'aux_626 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_writeStackMem'45'aux_626 v0 v1 v2 v3
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
d_writeStackMem_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_152) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_writeStackMem_634 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_626
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_648 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_648 v1 v2 v3 v4
du_writeHeapMem_648 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_648 v0 v1 v2 v3
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
d_writeLocToStack_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny -> Integer -> T_ValueLocation_152 -> T_LocState_450
d_writeLocToStack_678 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_470 (coe d_regs_462 (coe v1))
      (coe
         d_writeStackMem_634 (coe v0) (coe d_stackMem_464 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_466 (coe v1)) (coe d_halted_468 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
d_writeLocToHeap_688 ~v0 v1 v2 v3 = du_writeLocToHeap_688 v1 v2 v3
du_writeLocToHeap_688 ::
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
du_writeLocToHeap_688 v0 v1 v2
  = coe
      C_mkLocState_470 (coe d_regs_462 (coe v0))
      (coe d_stackMem_464 (coe v0))
      (coe
         du_writeHeapMem_648 (coe d_heapMem_466 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_468 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 -> T_ValueLocation_152 -> T_LocState_450
d_writeLoc_696 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_156 v4 v5
        -> coe
             d_writeLocToStack_678 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_158 v4
        -> case coe v3 of
             C_AtStack_156 v5 v6 -> coe v1
             C_AtDynamic_158 v5
               -> coe du_writeLocToHeap_688 (coe v1) (coe v4) (coe v5)
             C_InReg_160 v5 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_InReg_160 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_728 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_760 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_794 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_794 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_814 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  T_Registers_220 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_814 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_842 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_874 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1008 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1060 a0 = ()
data T_LocSourceExt_1060
  = C_Loc_1064 T_ValueLocation_152 |
    C_IndReg_1066 T_AbstractReg_142 |
    C_IndRegSuc_1068 T_AbstractReg_142
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_220 -> T_LocSourceExt_1060 -> T_ValueLocation_152
d_resolveSourceExt_1072 ~v0 v1 v2 = du_resolveSourceExt_1072 v1 v2
du_resolveSourceExt_1072 ::
  T_Registers_220 -> T_LocSourceExt_1060 -> T_ValueLocation_152
du_resolveSourceExt_1072 v0 v1
  = case coe v1 of
      C_Loc_1064 v2 -> coe v2
      C_IndReg_1066 v2 -> coe du_readReg_244 (coe v0) (coe v2)
      C_IndRegSuc_1068 v2
        -> coe du_sucLoc_178 (coe du_readReg_244 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1088 a0 = ()
data T_Instr_1088
  = C_load_1092 T_AbstractReg_142 T_LocSourceExt_1060 |
    C_store_1094 T_LocSourceExt_1060 T_AbstractReg_142 |
    C_mov_1096 T_AbstractReg_142 T_AbstractReg_142
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1104 ::
  T_LocState_450 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1104 v0 v1 = coe d_heapMem_466 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_readLoc_1106 ~v0 = du_readLoc_1106
du_readLoc_1106 ::
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_readLoc_1106 = coe du_readLoc_588
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1108 ::
  T_LocState_450 -> AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_readStackLoc_1108 v0 v1 v2 = coe d_stackMem_464 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1110 ~v0 = du_writeHeapMem_1110
du_writeHeapMem_1110 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1110 = coe du_writeHeapMem_648
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 -> T_ValueLocation_152 -> T_LocState_450
d_writeLoc_1112 v0 = coe d_writeLoc_696 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1114 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1116 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1116 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1118 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1120 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1122 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1124 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1126 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  T_Registers_220 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1126 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
d_writeLocToHeap_1128 ~v0 = du_writeLocToHeap_1128
du_writeLocToHeap_1128 ::
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
du_writeLocToHeap_1128 = coe du_writeLocToHeap_688
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny -> Integer -> T_ValueLocation_152 -> T_LocState_450
d_writeLocToStack_1130 v0 = coe d_writeLocToStack_678 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_152) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_writeStackMem_1132 v0 = coe d_writeStackMem_634 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_writeStackMem'45'aux_1134 ~v0 = du_writeStackMem'45'aux_1134
du_writeStackMem'45'aux_1134 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_writeStackMem'45'aux_1134 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_626 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
d_exec'45'load'45'with'45'value_1136 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1136 v1 v2
du_exec'45'load'45'with'45'value_1136 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
du_exec'45'load'45'with'45'value_1136 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_470 (coe du_writeReg_254 (d_regs_462 (coe v3)) v0 v2)
                  (coe d_stackMem_464 (coe v3)) (coe d_heapMem_466 (coe v3))
                  (coe d_halted_468 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_470 (coe d_regs_462 (coe v2))
                  (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1088 -> T_LocState_450 -> T_LocState_450
d_exec_1148 v0 v1
  = case coe v1 of
      C_load_1092 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1136 v2
                  (coe
                     du_readLoc_588 (coe v4)
                     (coe du_resolveSourceExt_1072 (coe d_regs_462 (coe v4)) (coe v3)))
                  v4)
      C_store_1094 v2 v3
        -> coe
             (\ v4 ->
                d_writeLoc_696
                  (coe v0) (coe v4)
                  (coe du_resolveSourceExt_1072 (coe d_regs_462 (coe v4)) (coe v2))
                  (coe du_readReg_244 (coe d_regs_462 (coe v4)) (coe v3)))
      C_mov_1096 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_470
                  (coe
                     du_writeReg_254 (d_regs_462 (coe v4)) v2
                     (coe du_readReg_244 (coe d_regs_462 (coe v4)) (coe v3)))
                  (coe d_stackMem_464 (coe v4)) (coe d_heapMem_466 (coe v4))
                  (coe d_halted_468 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1178 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1184 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1088] -> T_LocState_450 -> T_LocState_450
d_execList_1186 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_468 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1186 (coe v0) (coe v4) (coe d_exec_1148 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1218 ::
  T_LocState_450 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1218 v0 v1 = coe d_heapMem_466 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_readLoc_1220 ~v0 = du_readLoc_1220
du_readLoc_1220 ::
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_readLoc_1220 = coe du_readLoc_588
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1222 ::
  T_LocState_450 -> AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_readStackLoc_1222 v0 v1 v2 = coe d_stackMem_464 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1224 ~v0 = du_writeHeapMem_1224
du_writeHeapMem_1224 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1224 = coe du_writeHeapMem_648
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 -> T_ValueLocation_152 -> T_LocState_450
d_writeLoc_1226 v0 = coe d_writeLoc_696 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1228 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1230 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1230 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1232 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1234 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1236 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1238 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1240 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  T_Registers_220 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1240 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
d_writeLocToHeap_1242 ~v0 = du_writeLocToHeap_1242
du_writeLocToHeap_1242 ::
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
du_writeLocToHeap_1242 = coe du_writeLocToHeap_688
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny -> Integer -> T_ValueLocation_152 -> T_LocState_450
d_writeLocToStack_1244 v0 = coe d_writeLocToStack_678 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_152) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_writeStackMem_1246 v0 = coe d_writeStackMem_634 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_writeStackMem'45'aux_1248 ~v0 = du_writeStackMem'45'aux_1248
du_writeStackMem'45'aux_1248 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_writeStackMem'45'aux_1248 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_626 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1088 -> T_LocState_450 -> T_LocState_450
d_exec_1252 v0 = coe d_exec_1148 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1254 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1256 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
d_exec'45'load'45'with'45'value_1258 ~v0
  = du_exec'45'load'45'with'45'value_1258
du_exec'45'load'45'with'45'value_1258 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
du_exec'45'load'45'with'45'value_1258
  = coe du_exec'45'load'45'with'45'value_1136
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1088] -> T_LocState_450 -> T_LocState_450
d_execList_1260 v0 = coe d_execList_1186 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1270 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1308 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-preserves
d_load'45'failed'45'preserves_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1350 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1378 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1408 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1438 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 ->
  T_AbstractReg_142 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1454 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1472 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1486 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1502 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1536 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1556 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.inreg-readLoc-postulate
d_inreg'45'readLoc'45'postulate_1656
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.ExecLemmas._.inreg-readLoc-postulate"
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1658 = ()
data T_AbstractInstr_1658
  = C_mov'45'to'45'output_1660 | C_mov'45'to'45'input_1662 |
    C_mov'45'output'45'to'45'input2_1664 |
    C_mov'45'input2'45'to'45'output_1666 | C_load'45'indirect_1668 |
    C_load'45'indirect'45'suc_1670 |
    C_load'45'from'45'slot_1672 Integer |
    C_store'45'at'45'slot_1674 Integer | C_store'45'indirect_1676 |
    C_store'45'indirect'45'suc_1678 | C_lea'45'slot_1680 Integer |
    C_restore'45'input_1682 Integer |
    C_instr'45'alloc'45'stack_1684 Integer |
    C_instr'45'dealloc'45'stack_1686 Integer |
    C_instr'45'reclaim'45'to_1688 Integer |
    C_instr'45'push'45'frame_1690 Integer |
    C_instr'45'pop'45'frame_1692 | C_instr'45'call'45'closure_1694 |
    C_worklist'45'init_1696 Integer | C_worklist'45'push_1698 Integer |
    C_worklist'45'pop_1700 Integer | C_worklist'45'check_1702 Integer |
    C_instr'45'sigop_1708 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_264 |
    C_instr'45'load'45'const_1712 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_IsPrimitive_188 AgdaAny |
    C_instr'45'load'45'code'45'addr_1714 Integer |
    C_instr'45'save'45'closure'45'reg_1716
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1718 :: ()
d_AbstractTrace_1718 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_1720 = ()
data T_TreeTrace_1720
  = C_ε_1722 | C_instr_1724 T_AbstractInstr_1658 |
    C__'9656'__1726 T_TreeTrace_1720 T_TreeTrace_1720 |
    C_branch_1728 Integer T_TreeTrace_1720 T_TreeTrace_1720 |
    C_call'45'sub_1730 T_TreeTrace_1720 |
    C_flat_1732 [T_AbstractInstr_1658]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_1734 :: [T_AbstractInstr_1658] -> T_TreeTrace_1720
d_flatToTree_1734 v0
  = case coe v0 of
      [] -> coe C_ε_1722
      (:) v1 v2
        -> coe
             C__'9656'__1726 (coe C_instr_1724 (coe v1))
             (coe d_flatToTree_1734 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_1740 :: T_TreeTrace_1720 -> [T_AbstractInstr_1658]
d_treeToFlat_1740 v0
  = case coe v0 of
      C_ε_1722 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1724 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1726 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1740 (coe v1)) (coe d_treeToFlat_1740 (coe v2))
      C_branch_1728 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1740 (coe v2)) (coe d_treeToFlat_1740 (coe v3))
      C_call'45'sub_1730 v1 -> coe d_treeToFlat_1740 (coe v1)
      C_flat_1732 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_1756 ::
  Integer -> T_TreeTrace_1720 -> [T_AbstractInstr_1658]
d_treeToRunnable_1756 v0 v1
  = case coe v1 of
      C_ε_1722 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1724 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1726 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1756 (coe v0) (coe v2))
             (coe d_treeToRunnable_1756 (coe v0) (coe v3))
      C_branch_1728 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1756 (coe v0) (coe v3))
             (coe d_treeToRunnable_1756 (coe v0) (coe v4))
      C_call'45'sub_1730 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1698 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_1756 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1700 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_1732 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_1786 ::
  Integer -> T_TreeTrace_1720 -> [T_AbstractInstr_1658]
d_treeToRunnableWithInit_1786 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1696 (coe v0))
      (coe d_treeToRunnable_1756 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_1822 ::
  T_LocState_450 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1822 v0 v1 = coe d_heapMem_466 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_1824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_readLoc_1824 ~v0 = du_readLoc_1824
du_readLoc_1824 ::
  T_LocState_450 -> T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_readLoc_1824 = coe du_readLoc_588
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_1826 ::
  T_LocState_450 -> AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_readStackLoc_1826 v0 v1 v2 = coe d_stackMem_464 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_1828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1828 ~v0 = du_writeHeapMem_1828
du_writeHeapMem_1828 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1828 = coe du_writeHeapMem_648
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 -> T_ValueLocation_152 -> T_LocState_450
d_writeLoc_1830 v0 = coe d_writeLoc_696 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1832 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1834 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1834 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1836 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1838 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1840 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_1842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1842 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1844 ::
  T_LocState_450 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  T_Registers_220 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1844 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_1846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
d_writeLocToHeap_1846 ~v0 = du_writeLocToHeap_1846
du_writeLocToHeap_1846 ::
  T_LocState_450 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_450
du_writeLocToHeap_1846 = coe du_writeLocToHeap_688
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_1848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  AgdaAny -> Integer -> T_ValueLocation_152 -> T_LocState_450
d_writeLocToStack_1848 v0 = coe d_writeLocToStack_678 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_1850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_152) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_152 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_152
d_writeStackMem_1850 v0 = coe d_writeStackMem_634 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_1852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
d_writeStackMem'45'aux_1852 ~v0 = du_writeStackMem'45'aux_1852
du_writeStackMem'45'aux_1852 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_ValueLocation_152 ->
  T_ValueLocation_152 -> Maybe T_ValueLocation_152
du_writeStackMem'45'aux_1852 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_626 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1088 -> T_LocState_450 -> T_LocState_450
d_exec_1856 v0 = coe d_exec_1148 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_1858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1858 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1860 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
d_exec'45'load'45'with'45'value_1862 ~v0
  = du_exec'45'load'45'with'45'value_1862
du_exec'45'load'45'with'45'value_1862 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_450 -> T_LocState_450
du_exec'45'load'45'with'45'value_1862
  = coe du_exec'45'load'45'with'45'value_1136
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_1864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1088] -> T_LocState_450 -> T_LocState_450
d_execList_1864 v0 = coe d_execList_1186 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-preserves
d_load'45'failed'45'preserves_1868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1868 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_1870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1870 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_1872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1872 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1874 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_1876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_AbstractReg_142 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1876 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1878 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1060 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1880 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1882 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 ->
  T_AbstractReg_142 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1884 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1886 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_450 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1888 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 ->
  T_LocState_450 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1890 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1892 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1892 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_1892 ::
  Maybe T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1892 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe du_writeReg_254 (d_regs_462 (coe v1)) (coe C_Output_148) v3)
                (coe d_stackMem_464 (coe v1)) (coe d_heapMem_466 (coe v1))
                (coe d_halted_468 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470 (coe d_regs_462 (coe v1))
                (coe d_stackMem_464 (coe v1)) (coe d_heapMem_466 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1904 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_1904 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_1904 ::
  Maybe T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1904 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe du_writeReg_254 (d_regs_462 (coe v1)) (coe C_Input1_144) v3)
                (coe d_stackMem_464 (coe v1)) (coe d_heapMem_466 (coe v1))
                (coe d_halted_468 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470 (coe d_regs_462 (coe v1))
                (coe d_stackMem_464 (coe v1)) (coe d_heapMem_466 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1922 ::
  T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1922 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1928 ::
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1928 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1936 ::
  T_ValueLocation_152 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1936 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1942 ::
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1942 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_1948
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_1954
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts"
-- Once.CCC.Machine.SMCore.AbstractExec.encode-const
d_encode'45'const_1958
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.encode-const"
-- Once.CCC.Machine.SMCore.AbstractExec.encode-code-addr
d_encode'45'code'45'addr_1960
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.encode-code-addr"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_1962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1658 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1962 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1660
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input1_144)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1662
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Input1_144)
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_1664
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Input2_146)
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_1666
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input2_146)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_load'45'indirect_1668
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1136 (coe C_Output_148)
                (coe
                   du_readLoc_588 (coe v2)
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input1_144)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_1670
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1136 (coe C_Output_148)
                (coe
                   du_readLoc_588 (coe v2)
                   (coe
                      du_sucLoc_178
                      (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input1_144))))
                v2)
             (coe v3)
      C_load'45'from'45'slot_1672 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1892
             (coe
                du_readLoc_588 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1674 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_696 (coe v0) (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4))
                (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_store'45'indirect_1676
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_696 (coe v0) (coe v2)
                (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input1_144))
                (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_store'45'indirect'45'suc_1678
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_696 (coe v0) (coe v2)
                (coe
                   du_sucLoc_178
                   (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Input1_144)))
                (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_lea'45'slot_1680 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_restore'45'input_1682 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_1904
             (coe
                du_readLoc_588 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1684 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe du_incrStackSlot_278 (coe d_regs_462 (coe v2)) (coe v4))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe
                C_mkAllocState_544 (coe d_current'45'frame_538 (coe v3))
                (coe addInt (coe d_next'45'slot_540 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_542 (coe v3)))
      C_instr'45'dealloc'45'stack_1686 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe du_decrStackSlot_286 (coe d_regs_462 (coe v2)) (coe v4))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1688 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_544 (coe d_current'45'frame_538 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_542 (coe v3)))
      C_instr'45'push'45'frame_1690 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeStackSlot_270 (coe d_regs_462 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1692
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1694
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1696 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1698 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_696 (coe v0) (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4))
                (coe du_readReg_244 (coe d_regs_462 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_worklist'45'pop_1700 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1892
             (coe
                du_readLoc_588 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_538 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1702 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_1708 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe d_exec'45'sigop'45'output_1948 v0 v4 v5 v6 v2))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_exec'45'sigop'45'halts_1954 v0 v4 v5 v6 v2))
             (coe v3)
      C_instr'45'load'45'const_1712 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe d_encode'45'const_1958 v0 v4 v5 v6))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_1714 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_470
                (coe
                   du_writeReg_254 (d_regs_462 (coe v2)) (coe C_Output_148)
                   (coe d_encode'45'code'45'addr_1960 v0 v4))
                (coe d_stackMem_464 (coe v2)) (coe d_heapMem_466 (coe v2))
                (coe d_halted_468 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_1716
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1658] ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2100 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_468 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2100 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_1962 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_1962 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1658 ->
  [T_AbstractInstr_1658] ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2150 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1658 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2196 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_450 -> T_AllocState_480 -> Integer -> Maybe Integer
d_getTag_2230 ~v0 v1 v2 v3 = du_getTag_2230 v1 v2 v3
du_getTag_2230 ::
  T_LocState_450 -> T_AllocState_480 -> Integer -> Maybe Integer
du_getTag_2230 v0 v1 v2
  = let v3
          = coe d_stackMem_464 v0 (d_current'45'frame_538 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1720 ->
  T_LocState_450 ->
  T_AllocState_480 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2254 v0 v1 v2 v3
  = case coe v1 of
      C_ε_1722
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_1724 v4
        -> let v5 = d_halted_468 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_1962 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__1726 v4 v5
        -> let v6 = d_halted_468 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2254 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2254 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2254 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_1728 v4 v5 v6
        -> let v7 = d_halted_468 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_464 v2 (d_current'45'frame_538 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2254 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2254 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2254 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2254 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2254 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_1730 v4
        -> let v5 = d_halted_468 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2254 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_1732 v4
        -> coe d_exec'45'trace_2100 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2414 ::
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2414 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1720 ->
  T_TreeTrace_1720 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2432 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1658 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2478 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1720 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2518 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1658] ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2558 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1658] ->
  [T_AbstractInstr_1658] ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2578 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2636
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1720 ->
  T_LocState_450 ->
  T_AllocState_480 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2644 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2644
du_exec'45'tree'45'flat'45'equiv'45'simple_2644 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2644
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
