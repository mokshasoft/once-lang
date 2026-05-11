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
  = C_AtStack_156 AgdaAny Integer | C_AtDynamic_158 T_HeapLocation_54
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_162 a0 = ()
data T_StoredValue_162
  = C_SV'45'Ptr_166 T_ValueLocation_152 | C_SV'45'Tag_168 Integer |
    C_SV'45'Lit_172 MAlonzo.Code.Once.Type.T_Type_108
                    MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
    C_SV'45'Code_174 Integer
-- Once.CCC.Machine.SMCore.sucHL
d_sucHL_176 :: T_HeapLocation_54 -> T_HeapLocation_54
d_sucHL_176 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2
        -> coe
             C_heap'45'loc_64 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetHL
d_offsetHL_182 :: T_HeapLocation_54 -> Integer -> T_HeapLocation_54
d_offsetHL_182 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> coe C_heap'45'loc_64 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_152 -> T_ValueLocation_152
d_sucLoc_192 ~v0 v1 = du_sucLoc_192 v1
du_sucLoc_192 :: T_ValueLocation_152 -> T_ValueLocation_152
du_sucLoc_192 v0
  = case coe v0 of
      C_AtStack_156 v1 v2
        -> coe
             C_AtStack_156 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_AtDynamic_158 v1
        -> coe C_AtDynamic_158 (coe d_sucHL_176 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_152 -> Integer -> T_ValueLocation_152
d_offsetLoc_202 ~v0 v1 v2 = du_offsetLoc_202 v1 v2
du_offsetLoc_202 ::
  T_ValueLocation_152 -> Integer -> T_ValueLocation_152
du_offsetLoc_202 v0 v1
  = case coe v0 of
      C_AtStack_156 v2 v3
        -> coe C_AtStack_156 (coe v2) (coe addInt (coe v1) (coe v3))
      C_AtDynamic_158 v2
        -> coe C_AtDynamic_158 (coe d_offsetHL_182 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_216 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_220 :: ()
d_HeapMem_220 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__226 ::
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__226 v0 v1
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
d_Registers_230 a0 = ()
data T_Registers_230
  = C_mkRegs_250 T_StoredValue_162 T_StoredValue_162
                 T_StoredValue_162 Integer
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_242 :: T_Registers_230 -> T_StoredValue_162
d_input1_242 v0
  = case coe v0 of
      C_mkRegs_250 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_244 :: T_Registers_230 -> T_StoredValue_162
d_input2_244 v0
  = case coe v0 of
      C_mkRegs_250 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_246 :: T_Registers_230 -> T_StoredValue_162
d_output_246 v0
  = case coe v0 of
      C_mkRegs_250 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_248 :: T_Registers_230 -> Integer
d_stackSlot_248 v0
  = case coe v0 of
      C_mkRegs_250 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 -> T_AbstractReg_142 -> T_StoredValue_162
d_readReg_254 ~v0 v1 v2 = du_readReg_254 v1 v2
du_readReg_254 ::
  T_Registers_230 -> T_AbstractReg_142 -> T_StoredValue_162
du_readReg_254 v0 v1
  = case coe v1 of
      C_Input1_144 -> coe d_input1_242 (coe v0)
      C_Input2_146 -> coe d_input2_244 (coe v0)
      C_Output_148 -> coe d_output_246 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 ->
  T_AbstractReg_142 -> T_StoredValue_162 -> T_Registers_230
d_writeReg_264 ~v0 v1 v2 = du_writeReg_264 v1 v2
du_writeReg_264 ::
  T_Registers_230 ->
  T_AbstractReg_142 -> T_StoredValue_162 -> T_Registers_230
du_writeReg_264 v0 v1
  = case coe v1 of
      C_Input1_144
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_250 (coe v2) (coe d_input2_244 (coe v0))
                  (coe d_output_246 (coe v0)) (coe d_stackSlot_248 (coe v0)))
      C_Input2_146
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_250 (coe d_input1_242 (coe v0)) (coe v2)
                  (coe d_output_246 (coe v0)) (coe d_stackSlot_248 (coe v0)))
      C_Output_148
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_250 (coe d_input1_242 (coe v0))
                  (coe d_input2_244 (coe v0)) (coe v2)
                  (coe d_stackSlot_248 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 -> Integer -> T_Registers_230
d_writeStackSlot_280 ~v0 v1 v2 = du_writeStackSlot_280 v1 v2
du_writeStackSlot_280 ::
  T_Registers_230 -> Integer -> T_Registers_230
du_writeStackSlot_280 v0 v1
  = coe
      C_mkRegs_250 (coe d_input1_242 (coe v0))
      (coe d_input2_244 (coe v0)) (coe d_output_246 (coe v0)) (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 -> Integer -> T_Registers_230
d_incrStackSlot_288 ~v0 v1 v2 = du_incrStackSlot_288 v1 v2
du_incrStackSlot_288 ::
  T_Registers_230 -> Integer -> T_Registers_230
du_incrStackSlot_288 v0 v1
  = coe
      C_mkRegs_250 (coe d_input1_242 (coe v0))
      (coe d_input2_244 (coe v0)) (coe d_output_246 (coe v0))
      (coe addInt (coe d_stackSlot_248 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 -> Integer -> T_Registers_230
d_decrStackSlot_296 ~v0 v1 v2 = du_decrStackSlot_296 v1 v2
du_decrStackSlot_296 ::
  T_Registers_230 -> Integer -> T_Registers_230
du_decrStackSlot_296 v0 v1
  = coe
      C_mkRegs_250 (coe d_input1_242 (coe v0))
      (coe d_input2_244 (coe v0)) (coe d_output_246 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_248 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_316 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_392 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_414 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_438 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_460 a0 = ()
data T_LocState_460
  = C_mkLocState_480 T_Registers_230
                     (AgdaAny -> Integer -> Maybe T_StoredValue_162)
                     (T_HeapLocation_54 -> Maybe T_HeapLocation_54) Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_472 :: T_LocState_460 -> T_Registers_230
d_regs_472 v0
  = case coe v0 of
      C_mkLocState_480 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_474 ::
  T_LocState_460 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_stackMem_474 v0
  = case coe v0 of
      C_mkLocState_480 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_476 ::
  T_LocState_460 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_heapMem_476 v0
  = case coe v0 of
      C_mkLocState_480 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_478 :: T_LocState_460 -> Bool
d_halted_478 v0
  = case coe v0 of
      C_mkLocState_480 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_482 = ()
data T_AllocMode_482 = C_Stack_484 | C_Heap_486
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_490 a0 = ()
data T_AllocState_490 = C_mkAllocState_554 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_548 :: T_AllocState_490 -> AgdaAny
d_current'45'frame_548 v0
  = case coe v0 of
      C_mkAllocState_554 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_550 :: T_AllocState_490 -> Integer
d_next'45'slot_550 v0
  = case coe v0 of
      C_mkAllocState_554 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_552 :: T_AllocState_490 -> Integer
d_next'45'heap'45'ref_552 v0
  = case coe v0 of
      C_mkAllocState_554 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_584 ::
  T_LocState_460 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_readStackLoc_584 v0 v1 v2 = coe d_stackMem_474 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_592 ::
  T_LocState_460 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_592 v0 v1 = coe d_heapMem_476 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
d_readLoc_598 ~v0 v1 v2 = du_readLoc_598 v1 v2
du_readLoc_598 ::
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
du_readLoc_598 v0 v1
  = case coe v1 of
      C_AtStack_156 v2 v3 -> coe d_stackMem_474 v0 v2 v3
      C_AtDynamic_158 v2
        -> let v3 = coe d_heapMem_476 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_SV'45'Ptr_166 (coe C_AtDynamic_158 (coe v4)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
d_writeStackMem'45'aux_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_632 v5 v6 v7 v8
du_writeStackMem'45'aux_632 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
du_writeStackMem'45'aux_632 v0 v1 v2 v3
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
d_writeStackMem_640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_162) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_writeStackMem_640 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_632
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_654 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_654 v1 v2 v3 v4
du_writeHeapMem_654 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_654 v0 v1 v2 v3
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
d_writeLocToStack_684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny -> Integer -> T_StoredValue_162 -> T_LocState_460
d_writeLocToStack_684 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_480 (coe d_regs_472 (coe v1))
      (coe
         d_writeStackMem_640 (coe v0) (coe d_stackMem_474 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_476 (coe v1)) (coe d_halted_478 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
d_writeLocToHeap_694 ~v0 v1 v2 v3 = du_writeLocToHeap_694 v1 v2 v3
du_writeLocToHeap_694 ::
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
du_writeLocToHeap_694 v0 v1 v2
  = coe
      C_mkLocState_480 (coe d_regs_472 (coe v0))
      (coe d_stackMem_474 (coe v0))
      (coe
         du_writeHeapMem_654 (coe d_heapMem_476 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_478 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 -> T_StoredValue_162 -> T_LocState_460
d_writeLoc_702 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_156 v4 v5
        -> coe
             d_writeLocToStack_684 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_158 v4
        -> case coe v3 of
             C_SV'45'Ptr_166 v5
               -> case coe v5 of
                    C_AtStack_156 v6 v7 -> coe v1
                    C_AtDynamic_158 v6
                      -> coe du_writeLocToHeap_694 (coe v1) (coe v4) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Tag_168 v5 -> coe v1
             C_SV'45'Lit_172 v5 v6 v7 -> coe v1
             C_SV'45'Code_174 v5 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_740 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_778 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_818 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_818 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_838 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  T_Registers_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_838 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_866 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_898 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1036 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1088 a0 = ()
data T_LocSourceExt_1088
  = C_Loc_1092 T_ValueLocation_152 |
    C_IndReg_1094 T_AbstractReg_142 |
    C_IndRegSuc_1096 T_AbstractReg_142
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_162 -> Maybe T_ValueLocation_152
d_sv'45'as'45'loc_1100 ~v0 v1 = du_sv'45'as'45'loc_1100 v1
du_sv'45'as'45'loc_1100 ::
  T_StoredValue_162 -> Maybe T_ValueLocation_152
du_sv'45'as'45'loc_1100 v0
  = case coe v0 of
      C_SV'45'Ptr_166 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_168 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_172 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_174 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_230 -> T_LocSourceExt_1088 -> Maybe T_ValueLocation_152
d_resolveSourceExt_1106 ~v0 v1 v2 = du_resolveSourceExt_1106 v1 v2
du_resolveSourceExt_1106 ::
  T_Registers_230 -> T_LocSourceExt_1088 -> Maybe T_ValueLocation_152
du_resolveSourceExt_1106 v0 v1
  = case coe v1 of
      C_Loc_1092 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1094 v2
        -> coe
             du_sv'45'as'45'loc_1100 (coe du_readReg_254 (coe v0) (coe v2))
      C_IndRegSuc_1096 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1100 (coe du_readReg_254 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_192 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1136 a0 = ()
data T_Instr_1136
  = C_load_1140 T_AbstractReg_142 T_LocSourceExt_1088 |
    C_store_1142 T_LocSourceExt_1088 T_AbstractReg_142 |
    C_mov_1144 T_AbstractReg_142 T_AbstractReg_142
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1152 ::
  T_LocState_460 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1152 v0 v1 = coe d_heapMem_476 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
d_readLoc_1154 ~v0 = du_readLoc_1154
du_readLoc_1154 ::
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
du_readLoc_1154 = coe du_readLoc_598
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1156 ::
  T_LocState_460 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_readStackLoc_1156 v0 v1 v2 = coe d_stackMem_474 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
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
du_writeHeapMem_1158 = coe du_writeHeapMem_654
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 -> T_StoredValue_162 -> T_LocState_460
d_writeLoc_1160 v0 = coe d_writeLoc_702 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1162 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1164 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1164 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
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
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1168 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1170 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1172 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1174 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  T_Registers_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1174 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
d_writeLocToHeap_1176 ~v0 = du_writeLocToHeap_1176
du_writeLocToHeap_1176 ::
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
du_writeLocToHeap_1176 = coe du_writeLocToHeap_694
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny -> Integer -> T_StoredValue_162 -> T_LocState_460
d_writeLocToStack_1178 v0 = coe d_writeLocToStack_684 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_162) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_writeStackMem_1180 v0 = coe d_writeStackMem_640 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
d_writeStackMem'45'aux_1182 ~v0 = du_writeStackMem'45'aux_1182
du_writeStackMem'45'aux_1182 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
du_writeStackMem'45'aux_1182 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_632 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'with'45'value_1184 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1184 v1 v2
du_exec'45'load'45'with'45'value_1184 ::
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'with'45'value_1184 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_480 (coe du_writeReg_264 (d_regs_472 (coe v3)) v0 v2)
                  (coe d_stackMem_474 (coe v3)) (coe d_heapMem_476 (coe v3))
                  (coe d_halted_478 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_480 (coe d_regs_472 (coe v2))
                  (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'via'45'resolved_1196 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1196 v1 v2
du_exec'45'load'45'via'45'resolved_1196 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'via'45'resolved_1196 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1184 v0
                  (coe du_readLoc_598 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_480 (coe d_regs_472 (coe v2))
                  (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_152 ->
  T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'store'45'via'45'resolved_1208 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_702 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_480 (coe d_regs_472 (coe v3))
                  (coe d_stackMem_474 (coe v3)) (coe d_heapMem_476 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_460 -> T_LocState_460
d_exec_1218 v0 v1
  = case coe v1 of
      C_load_1140 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1196 v2
                  (coe du_resolveSourceExt_1106 (coe d_regs_472 (coe v4)) (coe v3))
                  v4)
      C_store_1142 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1208 v0
                  (coe du_resolveSourceExt_1106 (coe d_regs_472 (coe v4)) (coe v2))
                  (coe du_readReg_254 (coe d_regs_472 (coe v4)) (coe v3)) v4)
      C_mov_1144 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_480
                  (coe
                     du_writeReg_264 (d_regs_472 (coe v4)) v2
                     (coe du_readReg_254 (coe d_regs_472 (coe v4)) (coe v3)))
                  (coe d_stackMem_474 (coe v4)) (coe d_heapMem_476 (coe v4))
                  (coe d_halted_478 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1244 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1250 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_460 -> T_LocState_460
d_execList_1252 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_478 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1252 (coe v0) (coe v4) (coe d_exec_1218 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1284 ::
  T_LocState_460 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1284 v0 v1 = coe d_heapMem_476 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
d_readLoc_1286 ~v0 = du_readLoc_1286
du_readLoc_1286 ::
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
du_readLoc_1286 = coe du_readLoc_598
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1288 ::
  T_LocState_460 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_readStackLoc_1288 v0 v1 v2 = coe d_stackMem_474 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1290 ~v0 = du_writeHeapMem_1290
du_writeHeapMem_1290 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1290 = coe du_writeHeapMem_654
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 -> T_StoredValue_162 -> T_LocState_460
d_writeLoc_1292 v0 = coe d_writeLoc_702 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1294 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1296 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1296 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1298 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1300 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1302 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1304 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1306 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  T_Registers_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1306 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
d_writeLocToHeap_1308 ~v0 = du_writeLocToHeap_1308
du_writeLocToHeap_1308 ::
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
du_writeLocToHeap_1308 = coe du_writeLocToHeap_694
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny -> Integer -> T_StoredValue_162 -> T_LocState_460
d_writeLocToStack_1310 v0 = coe d_writeLocToStack_684 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_162) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_writeStackMem_1312 v0 = coe d_writeStackMem_640 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
d_writeStackMem'45'aux_1314 ~v0 = du_writeStackMem'45'aux_1314
du_writeStackMem'45'aux_1314 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
du_writeStackMem'45'aux_1314 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_632 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_460 -> T_LocState_460
d_exec_1318 v0 = coe d_exec_1218 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1320 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1322 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'via'45'resolved_1324 ~v0
  = du_exec'45'load'45'via'45'resolved_1324
du_exec'45'load'45'via'45'resolved_1324 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'via'45'resolved_1324
  = coe du_exec'45'load'45'via'45'resolved_1196
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'with'45'value_1326 ~v0
  = du_exec'45'load'45'with'45'value_1326
du_exec'45'load'45'with'45'value_1326 ::
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'with'45'value_1326
  = coe du_exec'45'load'45'with'45'value_1184
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_152 ->
  T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'store'45'via'45'resolved_1328 v0
  = coe d_exec'45'store'45'via'45'resolved_1208 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_460 -> T_LocState_460
d_execList_1330 v0 = coe d_execList_1252 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_162
d_resolved'45'readLoc_1332 ~v0 v1 v2
  = du_resolved'45'readLoc_1332 v1 v2
du_resolved'45'readLoc_1332 ::
  T_LocState_460 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_162
du_resolved'45'readLoc_1332 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1106 (coe d_regs_472 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_598 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1362 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1432 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1508 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1538 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1594 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1646 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1698 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 ->
  T_AbstractReg_142 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1714 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1732 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1746 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1764 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1830 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1854 = erased
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1934 = ()
data T_AbstractInstr_1934
  = C_mov'45'to'45'output_1936 | C_mov'45'to'45'input_1938 |
    C_mov'45'output'45'to'45'input2_1940 |
    C_mov'45'input2'45'to'45'output_1942 | C_load'45'indirect_1944 |
    C_load'45'indirect'45'suc_1946 |
    C_load'45'from'45'slot_1948 Integer |
    C_store'45'at'45'slot_1950 Integer | C_store'45'indirect_1952 |
    C_store'45'indirect'45'suc_1954 | C_lea'45'slot_1956 Integer |
    C_restore'45'input_1958 Integer |
    C_instr'45'alloc'45'stack_1960 Integer |
    C_instr'45'dealloc'45'stack_1962 Integer |
    C_instr'45'reclaim'45'to_1964 Integer |
    C_instr'45'push'45'frame_1966 Integer |
    C_instr'45'pop'45'frame_1968 | C_instr'45'call'45'closure_1970 |
    C_worklist'45'init_1972 Integer | C_worklist'45'push_1974 Integer |
    C_worklist'45'pop_1976 Integer | C_worklist'45'check_1978 Integer |
    C_instr'45'sigop_1984 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_264 |
    C_instr'45'load'45'const_1988 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
    C_instr'45'load'45'code'45'addr_1990 Integer |
    C_instr'45'save'45'closure'45'reg_1992 |
    C_instr'45'load'45'tag'45'lit_1994 Integer |
    C_instr'45'case'45'on'45'tag_1996 [T_AbstractInstr_1934]
                                      [T_AbstractInstr_1934]
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1998 :: ()
d_AbstractTrace_1998 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2000 = ()
data T_TreeTrace_2000
  = C_ε_2002 | C_instr_2004 T_AbstractInstr_1934 |
    C__'9656'__2006 T_TreeTrace_2000 T_TreeTrace_2000 |
    C_branch_2008 Integer T_TreeTrace_2000 T_TreeTrace_2000 |
    C_call'45'sub_2010 T_TreeTrace_2000 |
    C_flat_2012 [T_AbstractInstr_1934]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2014 :: [T_AbstractInstr_1934] -> T_TreeTrace_2000
d_flatToTree_2014 v0
  = case coe v0 of
      [] -> coe C_ε_2002
      (:) v1 v2
        -> coe
             C__'9656'__2006 (coe C_instr_2004 (coe v1))
             (coe d_flatToTree_2014 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2020 :: T_TreeTrace_2000 -> [T_AbstractInstr_1934]
d_treeToFlat_2020 v0
  = case coe v0 of
      C_ε_2002 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2004 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2006 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2020 (coe v1)) (coe d_treeToFlat_2020 (coe v2))
      C_branch_2008 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2020 (coe v2)) (coe d_treeToFlat_2020 (coe v3))
      C_call'45'sub_2010 v1 -> coe d_treeToFlat_2020 (coe v1)
      C_flat_2012 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2036 ::
  Integer -> T_TreeTrace_2000 -> [T_AbstractInstr_1934]
d_treeToRunnable_2036 v0 v1
  = case coe v1 of
      C_ε_2002 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2004 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2006 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2036 (coe v0) (coe v2))
             (coe d_treeToRunnable_2036 (coe v0) (coe v3))
      C_branch_2008 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2036 (coe v0) (coe v3))
             (coe d_treeToRunnable_2036 (coe v0) (coe v4))
      C_call'45'sub_2010 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1974 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2036 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1976 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2012 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2066 ::
  Integer -> T_TreeTrace_2000 -> [T_AbstractInstr_1934]
d_treeToRunnableWithInit_2066 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1972 (coe v0))
      (coe d_treeToRunnable_2036 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2102 ::
  T_LocState_460 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_2102 v0 v1 = coe d_heapMem_476 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
d_readLoc_2104 ~v0 = du_readLoc_2104
du_readLoc_2104 ::
  T_LocState_460 -> T_ValueLocation_152 -> Maybe T_StoredValue_162
du_readLoc_2104 = coe du_readLoc_598
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2106 ::
  T_LocState_460 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_readStackLoc_2106 v0 v1 v2 = coe d_stackMem_474 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_2108 ~v0 = du_writeHeapMem_2108
du_writeHeapMem_2108 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_2108 = coe du_writeHeapMem_654
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 -> T_StoredValue_162 -> T_LocState_460
d_writeLoc_2110 v0 = coe d_writeLoc_702 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2112 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2114 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2114 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2116 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2118 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2120 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2122 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2124 ::
  T_LocState_460 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 ->
  T_Registers_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2124 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
d_writeLocToHeap_2126 ~v0 = du_writeLocToHeap_2126
du_writeLocToHeap_2126 ::
  T_LocState_460 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_460
du_writeLocToHeap_2126 = coe du_writeLocToHeap_694
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  AgdaAny -> Integer -> T_StoredValue_162 -> T_LocState_460
d_writeLocToStack_2128 v0 = coe d_writeLocToStack_684 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_162) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_162 -> AgdaAny -> Integer -> Maybe T_StoredValue_162
d_writeStackMem_2130 v0 = coe d_writeStackMem_640 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
d_writeStackMem'45'aux_2132 ~v0 = du_writeStackMem'45'aux_2132
du_writeStackMem'45'aux_2132 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_162 ->
  T_StoredValue_162 -> Maybe T_StoredValue_162
du_writeStackMem'45'aux_2132 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_632 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1136 -> T_LocState_460 -> T_LocState_460
d_exec_2136 v0 = coe d_exec_1218 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2138 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2140 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'via'45'resolved_2142 ~v0
  = du_exec'45'load'45'via'45'resolved_2142
du_exec'45'load'45'via'45'resolved_2142 ::
  T_AbstractReg_142 ->
  Maybe T_ValueLocation_152 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'via'45'resolved_2142
  = coe du_exec'45'load'45'via'45'resolved_1196
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'load'45'with'45'value_2144 ~v0
  = du_exec'45'load'45'with'45'value_2144
du_exec'45'load'45'with'45'value_2144 ::
  T_AbstractReg_142 ->
  Maybe T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
du_exec'45'load'45'with'45'value_2144
  = coe du_exec'45'load'45'with'45'value_1184
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_152 ->
  T_StoredValue_162 -> T_LocState_460 -> T_LocState_460
d_exec'45'store'45'via'45'resolved_2146 v0
  = coe d_exec'45'store'45'via'45'resolved_1208 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1136] -> T_LocState_460 -> T_LocState_460
d_execList_2148 v0 = coe d_execList_1252 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2152 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2154 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2156 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2158 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2160 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_AbstractReg_142 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2162 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2164 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_LocSourceExt_1088 ->
  T_ValueLocation_152 ->
  T_LocState_460 ->
  T_StoredValue_162 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2166 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2168 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 ->
  T_AbstractReg_142 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2170 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2172 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_142 ->
  T_AbstractReg_142 ->
  T_LocState_460 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2174 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 ->
  T_LocState_460 ->
  T_ValueLocation_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2176 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_162
d_resolved'45'readLoc_2178 ~v0 = du_resolved'45'readLoc_2178
du_resolved'45'readLoc_2178 ::
  T_LocState_460 -> T_LocSourceExt_1088 -> Maybe T_StoredValue_162
du_resolved'45'readLoc_2178 = coe du_resolved'45'readLoc_1332
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2180 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2180 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2180 ::
  Maybe T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2180 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe du_writeReg_264 (d_regs_472 (coe v1)) (coe C_Output_148) v3)
                (coe d_stackMem_474 (coe v1)) (coe d_heapMem_476 (coe v1))
                (coe d_halted_478 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480 (coe d_regs_472 (coe v1))
                (coe d_stackMem_474 (coe v1)) (coe d_heapMem_476 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2192 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2192 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2192 ::
  Maybe T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2192 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe du_writeReg_264 (d_regs_472 (coe v1)) (coe C_Input1_144) v3)
                (coe d_stackMem_474 (coe v1)) (coe d_heapMem_476 (coe v1))
                (coe d_halted_478 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480 (coe d_regs_472 (coe v1))
                (coe d_stackMem_474 (coe v1)) (coe d_heapMem_476 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2210 ::
  T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2210 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2216 ::
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2216 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2224 ::
  T_StoredValue_162 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2224 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2230 ::
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2230 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2236
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2242
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1934 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2244 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1936
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Input1_144)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1938
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Input1_144)
                   (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_1940
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Input2_146)
                   (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_1942
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Input2_146)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_load'45'indirect_1944
        -> let v4
                 = coe
                     du_sv'45'as'45'loc_1100
                     (coe d_input1_242 (coe d_regs_472 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_exec'45'load'45'with'45'value_1184 (coe C_Output_148)
                          (coe du_readLoc_598 (coe v2) (coe v5)) v2)
                       (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_mkLocState_480 (coe d_regs_472 (coe v2))
                          (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_load'45'indirect'45'suc_1946
        -> let v4
                 = coe
                     du_sv'45'as'45'loc_1100
                     (coe d_input1_242 (coe d_regs_472 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          du_exec'45'load'45'with'45'value_1184 (coe C_Output_148)
                          (coe du_readLoc_598 (coe v2) (coe du_sucLoc_192 (coe v5))) v2)
                       (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_mkLocState_480 (coe d_regs_472 (coe v2))
                          (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_load'45'from'45'slot_1948 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2180
             (coe
                du_readLoc_598 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1950 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_702 (coe v0) (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4))
                (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_store'45'indirect_1952
        -> let v4
                 = coe
                     du_sv'45'as'45'loc_1100
                     (coe d_input1_242 (coe d_regs_472 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_writeLoc_702 (coe v0) (coe v2) (coe v5)
                          (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
                       (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_mkLocState_480 (coe d_regs_472 (coe v2))
                          (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_store'45'indirect'45'suc_1954
        -> let v4
                 = coe
                     du_sv'45'as'45'loc_1100
                     (coe d_input1_242 (coe d_regs_472 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_writeLoc_702 (coe v0) (coe v2) (coe du_sucLoc_192 (coe v5))
                          (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
                       (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_mkLocState_480 (coe d_regs_472 (coe v2))
                          (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_lea'45'slot_1956 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe
                      C_SV'45'Ptr_166
                      (coe
                         C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4))))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_restore'45'input_1958 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2192
             (coe
                du_readLoc_598 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1960 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe du_incrStackSlot_288 (coe d_regs_472 (coe v2)) (coe v4))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe
                C_mkAllocState_554 (coe d_current'45'frame_548 (coe v3))
                (coe addInt (coe d_next'45'slot_550 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_552 (coe v3)))
      C_instr'45'dealloc'45'stack_1962 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe du_decrStackSlot_296 (coe d_regs_472 (coe v2)) (coe v4))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1964 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_554 (coe d_current'45'frame_548 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_552 (coe v3)))
      C_instr'45'push'45'frame_1966 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeStackSlot_280 (coe d_regs_472 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1968
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1970
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1972 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1974 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_702 (coe v0) (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4))
                (coe du_readReg_254 (coe d_regs_472 (coe v2)) (coe C_Output_148)))
             (coe v3)
      C_worklist'45'pop_1976 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2180
             (coe
                du_readLoc_598 (coe v2)
                (coe C_AtStack_156 (coe d_current'45'frame_548 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1978 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_1984 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe d_exec'45'sigop'45'output_2236 v0 v4 v5 v6 v2))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_exec'45'sigop'45'halts_2242 v0 v4 v5 v6 v2))
             (coe v3)
      C_instr'45'load'45'const_1988 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe C_SV'45'Lit_172 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_1990 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe C_SV'45'Code_174 (coe v4)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_1992
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_1994 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480
                (coe
                   du_writeReg_264 (d_regs_472 (coe v2)) (coe C_Output_148)
                   (coe C_SV'45'Tag_168 (coe v4)))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe d_halted_478 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_1996 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_480 (coe d_regs_472 (coe v2))
                (coe d_stackMem_474 (coe v2)) (coe d_heapMem_476 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1934] ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2246 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_478 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2246 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2244 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2244 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1934 ->
  [T_AbstractInstr_1934] ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2502 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1934 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2548 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_460 -> T_AllocState_490 -> Integer -> Maybe Integer
d_getTag_2582 ~v0 v1 v2 v3 = du_getTag_2582 v1 v2 v3
du_getTag_2582 ::
  T_LocState_460 -> T_AllocState_490 -> Integer -> Maybe Integer
du_getTag_2582 v0 v1 v2
  = let v3
          = coe d_stackMem_474 v0 (d_current'45'frame_548 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2000 ->
  T_LocState_460 ->
  T_AllocState_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2606 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2002
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2004 v4
        -> let v5 = d_halted_478 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2244 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2006 v4 v5
        -> let v6 = d_halted_478 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2606 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2606 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2606 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2008 v4 v5 v6
        -> let v7 = d_halted_478 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_474 v2 (d_current'45'frame_548 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2606 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2606 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2606 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2606 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2606 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2010 v4
        -> let v5 = d_halted_478 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2606 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2012 v4
        -> coe d_exec'45'trace_2246 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2766 ::
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2766 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2000 ->
  T_TreeTrace_2000 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2784 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1934 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2830 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2000 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2870 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1934] ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2910 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1934] ->
  [T_AbstractInstr_1934] ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2930 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2988
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2000 ->
  T_LocState_460 ->
  T_AllocState_490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2996 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2996
du_exec'45'tree'45'flat'45'equiv'45'simple_2996 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2996
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
