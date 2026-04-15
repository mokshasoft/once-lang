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
-- Once.CCC.Machine.SMCore._≟HL_
d__'8799'HL__70 ::
  T_HeapLocation_54 ->
  T_HeapLocation_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__70 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> case coe v1 of
             C_heap'45'loc_64 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                               (coe eqInt (coe v3) (coe v5))) in
                  coe
                    (let v7
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v7 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_ref'45'id_24 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_ref'45'id_24 (coe v2))
                                     (coe d_ref'45'id_24 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_ref'45'id_24 (coe v2))
                                        (coe d_ref'45'id_24 (coe v4))))) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                            -> if coe v8
                                 then let v10
                                            = seq
                                                (coe v9)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                   (coe v8)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                      erased)) in
                                      coe
                                        (case coe v10 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                             -> if coe v11
                                                  then coe
                                                         seq (coe v12)
                                                         (case coe v6 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                              -> if coe v13
                                                                   then case coe v14 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v13)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe
                                                                                 seq (coe v13)
                                                                                 (coe
                                                                                    seq (coe v14)
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                                   else (case coe v14 of
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                             -> coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                           _ -> coe
                                                                                  seq (coe v13)
                                                                                  (coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v13)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  else coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 else (let v10
                                             = seq
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                       coe
                                         (case coe v10 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> if coe v11
                                                   then coe
                                                          seq (coe v12)
                                                          (case coe v6 of
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                               -> if coe v13
                                                                    then case coe v14 of
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                             -> coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                     erased)
                                                                           _ -> coe
                                                                                  seq (coe v13)
                                                                                  (coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v8)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                                    else (case coe v14 of
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                              -> coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                   (coe v13)
                                                                                   (coe
                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                            _ -> coe
                                                                                   seq (coe v13)
                                                                                   (coe
                                                                                      seq (coe v14)
                                                                                      (coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                         (coe v13)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))))
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   else coe
                                                          seq (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v11)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                            _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.hl-ref
d_hl'45'ref_116 :: T_HeapLocation_54 -> T_HeapRef_20
d_hl'45'ref_116 v0 = coe d_heap'45'ref_60 (coe v0)
-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_118 = ()
data T_HeapRegion_118 = C_heap'45'region_128 T_HeapRef_20 Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_124 :: T_HeapRegion_118 -> T_HeapRef_20
d_region'45'ref_124 v0
  = case coe v0 of
      C_heap'45'region_128 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_126 :: T_HeapRegion_118 -> Integer
d_region'45'size_126 v0
  = case coe v0 of
      C_heap'45'region_128 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_130 a0 a1 = ()
newtype T_InRegion_130
  = C_in'45'region_138 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_140 :: ()
d_HeapOwnership_140 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_142 a0 a1 = ()
data T_OutsideOwned_142
  = C_outside'45'nil_146 |
    C_outside'45'cons_154 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                          T_OutsideOwned_142
-- Once.CCC.Machine.SMCore.ValueLocation
d_ValueLocation_158 a0 = ()
data T_ValueLocation_158
  = C_OnStack_162 AgdaAny Integer | C_OnHeap_164 T_HeapLocation_54
-- Once.CCC.Machine.SMCore.sucHL
d_sucHL_166 :: T_HeapLocation_54 -> T_HeapLocation_54
d_sucHL_166 v0
  = case coe v0 of
      C_heap'45'loc_64 v1 v2
        -> coe
             C_heap'45'loc_64 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetHL
d_offsetHL_172 :: T_HeapLocation_54 -> Integer -> T_HeapLocation_54
d_offsetHL_172 v0 v1
  = case coe v0 of
      C_heap'45'loc_64 v2 v3
        -> coe C_heap'45'loc_64 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_158 -> T_ValueLocation_158
d_sucLoc_182 ~v0 v1 = du_sucLoc_182 v1
du_sucLoc_182 :: T_ValueLocation_158 -> T_ValueLocation_158
du_sucLoc_182 v0
  = case coe v0 of
      C_OnStack_162 v1 v2
        -> coe
             C_OnStack_162 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_OnHeap_164 v1 -> coe C_OnHeap_164 (coe d_sucHL_166 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_158 -> Integer -> T_ValueLocation_158
d_offsetLoc_192 ~v0 v1 v2 = du_offsetLoc_192 v1 v2
du_offsetLoc_192 ::
  T_ValueLocation_158 -> Integer -> T_ValueLocation_158
du_offsetLoc_192 v0 v1
  = case coe v0 of
      C_OnStack_162 v2 v3
        -> coe C_OnStack_162 (coe v2) (coe addInt (coe v1) (coe v3))
      C_OnHeap_164 v2
        -> coe C_OnHeap_164 (coe d_offsetHL_172 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_206 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_210 :: ()
d_HeapMem_210 = erased
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_212 = ()
data T_AbstractReg_212 = C_Input_214 | C_Output_216
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__222 ::
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__222 v0 v1
  = case coe v0 of
      C_Input_214
        -> case coe v1 of
             C_Input_214
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_216
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_216
        -> case coe v1 of
             C_Input_214
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_216
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_226 a0 = ()
data T_Registers_226
  = C_mkRegs_242 T_ValueLocation_158 T_ValueLocation_158 Integer
-- Once.CCC.Machine.SMCore.Registers.input
d_input_236 :: T_Registers_226 -> T_ValueLocation_158
d_input_236 v0
  = case coe v0 of
      C_mkRegs_242 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_238 :: T_Registers_226 -> T_ValueLocation_158
d_output_238 v0
  = case coe v0 of
      C_mkRegs_242 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_240 :: T_Registers_226 -> Integer
d_stackSlot_240 v0
  = case coe v0 of
      C_mkRegs_242 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 -> T_AbstractReg_212 -> T_ValueLocation_158
d_readReg_246 ~v0 v1 v2 = du_readReg_246 v1 v2
du_readReg_246 ::
  T_Registers_226 -> T_AbstractReg_212 -> T_ValueLocation_158
du_readReg_246 v0 v1
  = case coe v1 of
      C_Input_214 -> coe d_input_236 (coe v0)
      C_Output_216 -> coe d_output_238 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 ->
  T_AbstractReg_212 -> T_ValueLocation_158 -> T_Registers_226
d_writeReg_254 ~v0 v1 v2 = du_writeReg_254 v1 v2
du_writeReg_254 ::
  T_Registers_226 ->
  T_AbstractReg_212 -> T_ValueLocation_158 -> T_Registers_226
du_writeReg_254 v0 v1
  = case coe v1 of
      C_Input_214
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_242 (coe v2) (coe d_output_238 (coe v0))
                  (coe d_stackSlot_240 (coe v0)))
      C_Output_216
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_242 (coe d_input_236 (coe v0)) (coe v2)
                  (coe d_stackSlot_240 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 -> Integer -> T_Registers_226
d_writeStackSlot_266 ~v0 v1 v2 = du_writeStackSlot_266 v1 v2
du_writeStackSlot_266 ::
  T_Registers_226 -> Integer -> T_Registers_226
du_writeStackSlot_266 v0 v1
  = coe
      C_mkRegs_242 (coe d_input_236 (coe v0)) (coe d_output_238 (coe v0))
      (coe v1)
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 -> Integer -> T_Registers_226
d_incrStackSlot_274 ~v0 v1 v2 = du_incrStackSlot_274 v1 v2
du_incrStackSlot_274 ::
  T_Registers_226 -> Integer -> T_Registers_226
du_incrStackSlot_274 v0 v1
  = coe
      C_mkRegs_242 (coe d_input_236 (coe v0)) (coe d_output_238 (coe v0))
      (coe addInt (coe d_stackSlot_240 (coe v0)) (coe v1))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 -> Integer -> T_Registers_226
d_decrStackSlot_282 ~v0 v1 v2 = du_decrStackSlot_282 v1 v2
du_decrStackSlot_282 ::
  T_Registers_226 -> Integer -> T_Registers_226
du_decrStackSlot_282 v0 v1
  = coe
      C_mkRegs_242 (coe d_input_236 (coe v0)) (coe d_output_238 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_240 (coe v0)) v1)
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_302 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_344 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_362 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_382 = erased
-- Once.CCC.Machine.SMCore.LocState
d_LocState_398 a0 = ()
data T_LocState_398
  = C_mkLocState_418 T_Registers_226
                     (AgdaAny -> Integer -> Maybe T_ValueLocation_158)
                     (T_HeapLocation_54 -> Maybe T_HeapLocation_54) Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_410 :: T_LocState_398 -> T_Registers_226
d_regs_410 v0
  = case coe v0 of
      C_mkLocState_418 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_412 ::
  T_LocState_398 -> AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_stackMem_412 v0
  = case coe v0 of
      C_mkLocState_418 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_414 ::
  T_LocState_398 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_heapMem_414 v0
  = case coe v0 of
      C_mkLocState_418 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_416 :: T_LocState_398 -> Bool
d_halted_416 v0
  = case coe v0 of
      C_mkLocState_418 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_420 = ()
data T_AllocMode_420 = C_Stack_422 | C_Heap_424
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_428 a0 = ()
data T_AllocState_428 = C_mkAllocState_492 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_486 :: T_AllocState_428 -> AgdaAny
d_current'45'frame_486 v0
  = case coe v0 of
      C_mkAllocState_492 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_488 :: T_AllocState_428 -> Integer
d_next'45'slot_488 v0
  = case coe v0 of
      C_mkAllocState_492 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_490 :: T_AllocState_428 -> Integer
d_next'45'heap'45'ref_490 v0
  = case coe v0 of
      C_mkAllocState_492 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_522 ::
  T_LocState_398 -> AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_readStackLoc_522 v0 v1 v2 = coe d_stackMem_412 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_530 ::
  T_LocState_398 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_530 v0 v1 = coe d_heapMem_414 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
d_readLoc_536 ~v0 v1 v2 = du_readLoc_536 v1 v2
du_readLoc_536 ::
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
du_readLoc_536 v0 v1
  = case coe v1 of
      C_OnStack_162 v2 v3 -> coe d_stackMem_412 v0 v2 v3
      C_OnHeap_164 v2
        -> let v3 = coe d_heapMem_414 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_OnHeap_164 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem
d_writeStackMem_562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_158) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_writeStackMem_562 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5 in
    coe
      (let v8
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v8 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe v3))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                    (coe eqInt (coe v3) (coe v6))) in
       coe
         (case coe v7 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
              -> let v11 = coe v1 v5 v6 in
                 coe
                   (case coe v9 of
                      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                        -> case coe v10 of
                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                               -> case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                             -> case coe v14 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe v4)
                                                  _ -> coe v11
                                           _ -> coe v11
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> coe v11
                      _ -> coe v11)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_604 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_604 v1 v2 v3 v4
du_writeHeapMem_604 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_604 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v4 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_heap'45'offset_62 (coe v1)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_heap'45'offset_62 (coe v1))
                    (coe d_heap'45'offset_62 (coe v3)))) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v5 ->
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
         (case coe v5 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
              -> if coe v6
                   then let v8
                              = seq
                                  (coe v7)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                        erased)) in
                        coe
                          (case coe v8 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> if coe v9
                                    then let v11
                                               = seq
                                                   (coe v10)
                                                   (case coe v4 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                        -> if coe v11
                                                             then case coe v12 of
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                      -> coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                           (coe v11)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                              erased)
                                                                    _ -> coe
                                                                           seq (coe v11)
                                                                           (coe
                                                                              seq (coe v12)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                             else (case coe v12 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                       -> coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe v11)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                     _ -> coe
                                                                            seq (coe v11)
                                                                            (coe
                                                                               seq (coe v12)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                  (coe v11)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                -> if coe v12
                                                     then coe
                                                            seq (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                               (coe v2))
                                                     else coe seq (coe v13) (coe v0 v3)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    else (let v11
                                                = seq
                                                    (coe v10)
                                                    (coe
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                       (coe v9)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                          coe
                                            (case coe v11 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                 -> if coe v12
                                                      then coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe v2))
                                                      else coe seq (coe v13) (coe v0 v3)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else (let v8
                               = seq
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                      (coe v6)
                                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then let v11
                                                = seq
                                                    (coe v10)
                                                    (case coe v4 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                         -> if coe v11
                                                              then case coe v12 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                       -> coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe v11)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                               erased)
                                                                     _ -> coe
                                                                            seq (coe v11)
                                                                            (coe
                                                                               seq (coe v12)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                  (coe v6)
                                                                                  (coe
                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                              else (case coe v12 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                        -> coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v11)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                      _ -> coe
                                                                             seq (coe v11)
                                                                             (coe
                                                                                seq (coe v12)
                                                                                (coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                   (coe v11)
                                                                                   (coe
                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))))
                                                       _ -> MAlonzo.RTE.mazUnreachableError) in
                                          coe
                                            (case coe v11 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                 -> if coe v12
                                                      then coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe v2))
                                                      else coe seq (coe v13) (coe v0 v3)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     else (let v11
                                                 = seq
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                           coe
                                             (case coe v11 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                  -> if coe v12
                                                       then coe
                                                              seq (coe v13)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe v2))
                                                       else coe seq (coe v13) (coe v0 v3)
                                                _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny -> Integer -> T_ValueLocation_158 -> T_LocState_398
d_writeLocToStack_634 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_418 (coe d_regs_410 (coe v1))
      (coe
         d_writeStackMem_562 (coe v0) (coe d_stackMem_412 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_414 (coe v1)) (coe d_halted_416 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
d_writeLocToHeap_644 ~v0 v1 v2 v3 = du_writeLocToHeap_644 v1 v2 v3
du_writeLocToHeap_644 ::
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
du_writeLocToHeap_644 v0 v1 v2
  = coe
      C_mkLocState_418 (coe d_regs_410 (coe v0))
      (coe d_stackMem_412 (coe v0))
      (coe
         du_writeHeapMem_604 (coe d_heapMem_414 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_416 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 -> T_ValueLocation_158 -> T_LocState_398
d_writeLoc_652 v0 v1 v2 v3
  = case coe v2 of
      C_OnStack_162 v4 v5
        -> coe
             d_writeLocToStack_634 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_OnHeap_164 v4
        -> case coe v3 of
             C_OnStack_162 v5 v6 -> coe v1
             C_OnHeap_164 v5
               -> coe du_writeLocToHeap_644 (coe v1) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_678 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_704 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_732 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_732 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_752 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  T_Registers_226 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_752 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_772 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_918 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_970 a0 = ()
data T_LocSourceExt_970
  = C_Loc_974 T_ValueLocation_158 | C_IndReg_976 T_AbstractReg_212 |
    C_IndRegSuc_978 T_AbstractReg_212
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_226 -> T_LocSourceExt_970 -> T_ValueLocation_158
d_resolveSourceExt_982 ~v0 v1 v2 = du_resolveSourceExt_982 v1 v2
du_resolveSourceExt_982 ::
  T_Registers_226 -> T_LocSourceExt_970 -> T_ValueLocation_158
du_resolveSourceExt_982 v0 v1
  = case coe v1 of
      C_Loc_974 v2 -> coe v2
      C_IndReg_976 v2 -> coe du_readReg_246 (coe v0) (coe v2)
      C_IndRegSuc_978 v2
        -> coe du_sucLoc_182 (coe du_readReg_246 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_998 a0 = ()
data T_Instr_998
  = C_load_1002 T_AbstractReg_212 T_LocSourceExt_970 |
    C_store_1004 T_LocSourceExt_970 T_AbstractReg_212 |
    C_mov_1006 T_AbstractReg_212 T_AbstractReg_212
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1014 ::
  T_LocState_398 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1014 v0 v1 = coe d_heapMem_414 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
d_readLoc_1016 ~v0 = du_readLoc_1016
du_readLoc_1016 ::
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
du_readLoc_1016 = coe du_readLoc_536
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1018 ::
  T_LocState_398 -> AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_readStackLoc_1018 v0 v1 v2 = coe d_stackMem_412 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1020 ~v0 = du_writeHeapMem_1020
du_writeHeapMem_1020 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1020 = coe du_writeHeapMem_604
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 -> T_ValueLocation_158 -> T_LocState_398
d_writeLoc_1022 v0 = coe d_writeLoc_652 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1024 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1026 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1026 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1028 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1030 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1032 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1034 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  T_Registers_226 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1034 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
d_writeLocToHeap_1036 ~v0 = du_writeLocToHeap_1036
du_writeLocToHeap_1036 ::
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
du_writeLocToHeap_1036 = coe du_writeLocToHeap_644
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny -> Integer -> T_ValueLocation_158 -> T_LocState_398
d_writeLocToStack_1038 v0 = coe d_writeLocToStack_634 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_158) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_writeStackMem_1040 v0 = coe d_writeStackMem_562 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1042 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
d_exec'45'load'45'with'45'value_1042 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1042 v1 v2
du_exec'45'load'45'with'45'value_1042 ::
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
du_exec'45'load'45'with'45'value_1042 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_418 (coe du_writeReg_254 (d_regs_410 (coe v3)) v0 v2)
                  (coe d_stackMem_412 (coe v3)) (coe d_heapMem_414 (coe v3))
                  (coe d_halted_416 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_418 (coe d_regs_410 (coe v2))
                  (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_998 -> T_LocState_398 -> T_LocState_398
d_exec_1054 v0 v1
  = case coe v1 of
      C_load_1002 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'with'45'value_1042 v2
                  (coe
                     du_readLoc_536 (coe v4)
                     (coe du_resolveSourceExt_982 (coe d_regs_410 (coe v4)) (coe v3)))
                  v4)
      C_store_1004 v2 v3
        -> coe
             (\ v4 ->
                d_writeLoc_652
                  (coe v0) (coe v4)
                  (coe du_resolveSourceExt_982 (coe d_regs_410 (coe v4)) (coe v2))
                  (coe du_readReg_246 (coe d_regs_410 (coe v4)) (coe v3)))
      C_mov_1006 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_418
                  (coe
                     du_writeReg_254 (d_regs_410 (coe v4)) v2
                     (coe du_readReg_246 (coe d_regs_410 (coe v4)) (coe v3)))
                  (coe d_stackMem_412 (coe v4)) (coe d_heapMem_414 (coe v4))
                  (coe d_halted_416 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1084 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1090 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1090 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_998] -> T_LocState_398 -> T_LocState_398
d_execList_1092 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_416 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1092 (coe v0) (coe v4) (coe d_exec_1054 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1124 ::
  T_LocState_398 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1124 v0 v1 = coe d_heapMem_414 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
d_readLoc_1126 ~v0 = du_readLoc_1126
du_readLoc_1126 ::
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
du_readLoc_1126 = coe du_readLoc_536
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1128 ::
  T_LocState_398 -> AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_readStackLoc_1128 v0 v1 v2 = coe d_stackMem_412 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1130 ~v0 = du_writeHeapMem_1130
du_writeHeapMem_1130 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1130 = coe du_writeHeapMem_604
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 -> T_ValueLocation_158 -> T_LocState_398
d_writeLoc_1132 v0 = coe d_writeLoc_652 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1134 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1136 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1136 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1138 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1140 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1142 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1144 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  T_Registers_226 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1144 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
d_writeLocToHeap_1146 ~v0 = du_writeLocToHeap_1146
du_writeLocToHeap_1146 ::
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
du_writeLocToHeap_1146 = coe du_writeLocToHeap_644
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny -> Integer -> T_ValueLocation_158 -> T_LocState_398
d_writeLocToStack_1148 v0 = coe d_writeLocToStack_634 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_158) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_writeStackMem_1150 v0 = coe d_writeStackMem_562 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_998 -> T_LocState_398 -> T_LocState_398
d_exec_1154 v0 = coe d_exec_1054 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1156 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1158 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
d_exec'45'load'45'with'45'value_1160 ~v0
  = du_exec'45'load'45'with'45'value_1160
du_exec'45'load'45'with'45'value_1160 ::
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
du_exec'45'load'45'with'45'value_1160
  = coe du_exec'45'load'45'with'45'value_1042
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_998] -> T_LocState_398 -> T_LocState_398
d_execList_1162 v0 = coe d_execList_1092 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1172 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1210 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-preserves
d_load'45'failed'45'preserves_1252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1252 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1280 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1310 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1340 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 ->
  T_AbstractReg_212 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1356 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1374 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1388 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1404 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1438 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1458 = erased
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_1538 = ()
data T_AbstractInstr_1538
  = C_mov'45'to'45'output_1540 | C_mov'45'to'45'input_1542 |
    C_load'45'indirect_1544 | C_load'45'indirect'45'suc_1546 |
    C_load'45'from'45'slot_1548 Integer |
    C_store'45'at'45'slot_1550 Integer | C_store'45'indirect_1552 |
    C_store'45'indirect'45'suc_1554 | C_lea'45'slot_1556 Integer |
    C_restore'45'input_1558 Integer |
    C_instr'45'alloc'45'stack_1560 Integer |
    C_instr'45'dealloc'45'stack_1562 Integer |
    C_instr'45'reclaim'45'to_1564 Integer |
    C_instr'45'push'45'frame_1566 Integer |
    C_instr'45'pop'45'frame_1568 | C_instr'45'call'45'closure_1570 |
    C_worklist'45'init_1572 Integer | C_worklist'45'push_1574 Integer |
    C_worklist'45'pop_1576 Integer | C_worklist'45'check_1578 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_1580 :: ()
d_AbstractTrace_1580 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_1582 = ()
data T_TreeTrace_1582
  = C_ε_1584 | C_instr_1586 T_AbstractInstr_1538 |
    C__'9656'__1588 T_TreeTrace_1582 T_TreeTrace_1582 |
    C_branch_1590 Integer T_TreeTrace_1582 T_TreeTrace_1582 |
    C_call'45'sub_1592 T_TreeTrace_1582 |
    C_flat_1594 [T_AbstractInstr_1538]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_1596 :: [T_AbstractInstr_1538] -> T_TreeTrace_1582
d_flatToTree_1596 v0
  = case coe v0 of
      [] -> coe C_ε_1584
      (:) v1 v2
        -> coe
             C__'9656'__1588 (coe C_instr_1586 (coe v1))
             (coe d_flatToTree_1596 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_1602 :: T_TreeTrace_1582 -> [T_AbstractInstr_1538]
d_treeToFlat_1602 v0
  = case coe v0 of
      C_ε_1584 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1586 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1588 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1602 (coe v1)) (coe d_treeToFlat_1602 (coe v2))
      C_branch_1590 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_1602 (coe v2)) (coe d_treeToFlat_1602 (coe v3))
      C_call'45'sub_1592 v1 -> coe d_treeToFlat_1602 (coe v1)
      C_flat_1594 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_1618 ::
  Integer -> T_TreeTrace_1582 -> [T_AbstractInstr_1538]
d_treeToRunnable_1618 v0 v1
  = case coe v1 of
      C_ε_1584 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_1586 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__1588 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1618 (coe v0) (coe v2))
             (coe d_treeToRunnable_1618 (coe v0) (coe v3))
      C_branch_1590 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_1618 (coe v0) (coe v3))
             (coe d_treeToRunnable_1618 (coe v0) (coe v4))
      C_call'45'sub_1592 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_1574 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_1618 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_1576 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_1594 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_1648 ::
  Integer -> T_TreeTrace_1582 -> [T_AbstractInstr_1538]
d_treeToRunnableWithInit_1648 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_1572 (coe v0))
      (coe d_treeToRunnable_1618 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_1684 ::
  T_LocState_398 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_readHeapLoc_1684 v0 v1 = coe d_heapMem_414 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
d_readLoc_1686 ~v0 = du_readLoc_1686
du_readLoc_1686 ::
  T_LocState_398 -> T_ValueLocation_158 -> Maybe T_ValueLocation_158
du_readLoc_1686 = coe du_readLoc_536
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_1688 ::
  T_LocState_398 -> AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_readStackLoc_1688 v0 v1 v2 = coe d_stackMem_412 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
d_writeHeapMem_1690 ~v0 = du_writeHeapMem_1690
du_writeHeapMem_1690 ::
  (T_HeapLocation_54 -> Maybe T_HeapLocation_54) ->
  T_HeapLocation_54 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> Maybe T_HeapLocation_54
du_writeHeapMem_1690 = coe du_writeHeapMem_604
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 -> T_ValueLocation_158 -> T_LocState_398
d_writeLoc_1692 v0 = coe d_writeLoc_652 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1694 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1696 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1696 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1698 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1700 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1702 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1704 ::
  T_LocState_398 ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  T_Registers_226 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1704 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
d_writeLocToHeap_1706 ~v0 = du_writeLocToHeap_1706
du_writeLocToHeap_1706 ::
  T_LocState_398 ->
  T_HeapLocation_54 -> T_HeapLocation_54 -> T_LocState_398
du_writeLocToHeap_1706 = coe du_writeLocToHeap_644
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  AgdaAny -> Integer -> T_ValueLocation_158 -> T_LocState_398
d_writeLocToStack_1708 v0 = coe d_writeLocToStack_634 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_158) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_158 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_158
d_writeStackMem_1710 v0 = coe d_writeStackMem_562 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_998 -> T_LocState_398 -> T_LocState_398
d_exec_1714 v0 = coe d_exec_1054 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1716 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1718 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
d_exec'45'load'45'with'45'value_1720 ~v0
  = du_exec'45'load'45'with'45'value_1720
du_exec'45'load'45'with'45'value_1720 ::
  T_AbstractReg_212 ->
  Maybe T_ValueLocation_158 -> T_LocState_398 -> T_LocState_398
du_exec'45'load'45'with'45'value_1720
  = coe du_exec'45'load'45'with'45'value_1042
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_998] -> T_LocState_398 -> T_LocState_398
d_execList_1722 v0 = coe d_execList_1092 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-preserves
d_load'45'failed'45'preserves_1726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_1726 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_1728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1728 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_1730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1730 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1732 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_1734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_AbstractReg_212 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1734 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1736 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_1738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_LocSourceExt_970 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1738 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1740 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 ->
  T_AbstractReg_212 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1742 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1744 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_1746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_212 ->
  T_AbstractReg_212 ->
  T_LocState_398 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1746 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 ->
  T_LocState_398 ->
  T_ValueLocation_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1748 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_1750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_1750 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_1750 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_1750 ::
  Maybe T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_1750 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe du_writeReg_254 (d_regs_410 (coe v1)) (coe C_Output_216) v3)
                (coe d_stackMem_412 (coe v1)) (coe d_heapMem_414 (coe v1))
                (coe d_halted_416 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418 (coe d_regs_410 (coe v1))
                (coe d_stackMem_412 (coe v1)) (coe d_heapMem_414 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_1762 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_1762 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_1762 ::
  Maybe T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_1762 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe du_writeReg_254 (d_regs_410 (coe v1)) (coe C_Input_214) v3)
                (coe d_stackMem_412 (coe v1)) (coe d_heapMem_414 (coe v1))
                (coe d_halted_416 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418 (coe d_regs_410 (coe v1))
                (coe d_stackMem_412 (coe v1)) (coe d_heapMem_414 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_1780 ::
  T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_1780 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_1786 ::
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_1786 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_1794 ::
  T_ValueLocation_158 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_1794 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_1800 ::
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_1800 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_1802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1538 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_1802 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_1540
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe
                   du_writeReg_254 (d_regs_410 (coe v2)) (coe C_Output_216)
                   (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Input_214)))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_1542
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe
                   du_writeReg_254 (d_regs_410 (coe v2)) (coe C_Input_214)
                   (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Output_216)))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe v3)
      C_load'45'indirect_1544
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1042 (coe C_Output_216)
                (coe
                   du_readLoc_536 (coe v2)
                   (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Input_214)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_1546
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'with'45'value_1042 (coe C_Output_216)
                (coe
                   du_readLoc_536 (coe v2)
                   (coe
                      du_sucLoc_182
                      (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Input_214))))
                v2)
             (coe v3)
      C_load'45'from'45'slot_1548 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1750
             (coe
                du_readLoc_536 (coe v2)
                (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_1550 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_652 (coe v0) (coe v2)
                (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4))
                (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Output_216)))
             (coe v3)
      C_store'45'indirect_1552
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_652 (coe v0) (coe v2)
                (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Input_214))
                (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Output_216)))
             (coe v3)
      C_store'45'indirect'45'suc_1554
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_652 (coe v0) (coe v2)
                (coe
                   du_sucLoc_182
                   (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Input_214)))
                (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Output_216)))
             (coe v3)
      C_lea'45'slot_1556 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe
                   du_writeReg_254 (d_regs_410 (coe v2)) (coe C_Output_216)
                   (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4)))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe v3)
      C_restore'45'input_1558 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_1762
             (coe
                du_readLoc_536 (coe v2)
                (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_1560 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe du_incrStackSlot_274 (coe d_regs_410 (coe v2)) (coe v4))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe
                C_mkAllocState_492 (coe d_current'45'frame_486 (coe v3))
                (coe addInt (coe d_next'45'slot_488 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_490 (coe v3)))
      C_instr'45'dealloc'45'stack_1562 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe du_decrStackSlot_282 (coe d_regs_410 (coe v2)) (coe v4))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_1564 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_492 (coe d_current'45'frame_486 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_490 (coe v3)))
      C_instr'45'push'45'frame_1566 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_418
                (coe
                   du_writeStackSlot_266 (coe d_regs_410 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_412 (coe v2)) (coe d_heapMem_414 (coe v2))
                (coe d_halted_416 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_1568
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_1570
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_1572 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_1574 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_652 (coe v0) (coe v2)
                (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4))
                (coe du_readReg_246 (coe d_regs_410 (coe v2)) (coe C_Output_216)))
             (coe v3)
      C_worklist'45'pop_1576 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_1750
             (coe
                du_readLoc_536 (coe v2)
                (coe C_OnStack_162 (coe d_current'45'frame_486 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_1578 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_1908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1538] ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_1908 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_416 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_1908 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_1802 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_1802 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_1958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1538 ->
  [T_AbstractInstr_1538] ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_1958 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1538 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2004 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_398 -> T_AllocState_428 -> Integer -> Maybe Integer
d_getTag_2038 ~v0 v1 v2 v3 = du_getTag_2038 v1 v2 v3
du_getTag_2038 ::
  T_LocState_398 -> T_AllocState_428 -> Integer -> Maybe Integer
du_getTag_2038 v0 v1 v2
  = let v3
          = coe d_stackMem_412 v0 (d_current'45'frame_486 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1582 ->
  T_LocState_398 ->
  T_AllocState_428 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2062 v0 v1 v2 v3
  = case coe v1 of
      C_ε_1584
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_1586 v4
        -> let v5 = d_halted_416 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_1802 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__1588 v4 v5
        -> let v6 = d_halted_416 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2062 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2062 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2062 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_1590 v4 v5 v6
        -> let v7 = d_halted_416 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_412 v2 (d_current'45'frame_486 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (let v11
                                         = d_exec'45'tree'45'trace_2062
                                             (coe v0) (coe v6) (coe v2) (coe v3) in
                                   coe
                                     (case coe v10 of
                                        0 -> coe
                                               d_exec'45'tree'45'trace_2062 (coe v0) (coe v5)
                                               (coe v2) (coe v3)
                                        _ -> coe v11))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> let v10
                                             = d_exec'45'tree'45'trace_2062
                                                 (coe v0) (coe v6) (coe v2) (coe v3) in
                                       coe
                                         (case coe v9 of
                                            0 -> coe
                                                   d_exec'45'tree'45'trace_2062 (coe v0) (coe v5)
                                                   (coe v2) (coe v3)
                                            _ -> coe v10)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2062 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_1592 v4
        -> let v5 = d_halted_416 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2062 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_1594 v4
        -> coe d_exec'45'trace_1908 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_2222 ::
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_2222 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1582 ->
  T_TreeTrace_1582 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_2240 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_2286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_1538 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_2286 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_2326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1582 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_2326 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_2366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1538] ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_2366 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_2386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_1538] ->
  [T_AbstractInstr_1538] ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_2386 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_2444
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_2452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_1582 ->
  T_LocState_398 ->
  T_AllocState_428 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_2452 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_2452
du_exec'45'tree'45'flat'45'equiv'45'simple_2452 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_2452
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
