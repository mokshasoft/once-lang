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

module MAlonzo.Code.Once.CCC.SlotMachine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.SlotMachine.Slot
d_Slot_6 :: ()
d_Slot_6 = erased
-- Once.CCC.SlotMachine.HeapOffset
d_HeapOffset_8 :: ()
d_HeapOffset_8 = erased
-- Once.CCC.SlotMachine.HeapRef
d_HeapRef_10 = ()
newtype T_HeapRef_10 = C_mkHeapRef_16 Integer
-- Once.CCC.SlotMachine.HeapRef.ref-id
d_ref'45'id_14 :: T_HeapRef_10 -> Integer
d_ref'45'id_14 v0
  = case coe v0 of
      C_mkHeapRef_16 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine._≟H_
d__'8799'H__22 ::
  T_HeapRef_10 ->
  T_HeapRef_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'H__22 v0 v1
  = case coe v0 of
      C_mkHeapRef_16 v2
        -> case coe v1 of
             C_mkHeapRef_16 v3
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
-- Once.CCC.SlotMachine.HeapLocation
d_HeapLocation_44 = ()
data T_HeapLocation_44 = C_heap'45'loc_54 T_HeapRef_10 Integer
-- Once.CCC.SlotMachine.HeapLocation.heap-ref
d_heap'45'ref_50 :: T_HeapLocation_44 -> T_HeapRef_10
d_heap'45'ref_50 v0
  = case coe v0 of
      C_heap'45'loc_54 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.HeapLocation.heap-offset
d_heap'45'offset_52 :: T_HeapLocation_44 -> Integer
d_heap'45'offset_52 v0
  = case coe v0 of
      C_heap'45'loc_54 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine._≟HL_
d__'8799'HL__60 ::
  T_HeapLocation_44 ->
  T_HeapLocation_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__60 v0 v1
  = case coe v0 of
      C_heap'45'loc_54 v2 v3
        -> case coe v1 of
             C_heap'45'loc_54 v4 v5
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
                                    (coe d_ref'45'id_14 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_ref'45'id_14 (coe v2))
                                     (coe d_ref'45'id_14 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_ref'45'id_14 (coe v2))
                                        (coe d_ref'45'id_14 (coe v4))))) in
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
-- Once.CCC.SlotMachine.hl-ref
d_hl'45'ref_106 :: T_HeapLocation_44 -> T_HeapRef_10
d_hl'45'ref_106 v0 = coe d_heap'45'ref_50 (coe v0)
-- Once.CCC.SlotMachine.ValueLocation
d_ValueLocation_110 a0 = ()
data T_ValueLocation_110
  = C_OnStack_114 AgdaAny Integer | C_OnHeap_116 T_HeapLocation_44
-- Once.CCC.SlotMachine.sucHL
d_sucHL_118 :: T_HeapLocation_44 -> T_HeapLocation_44
d_sucHL_118 v0
  = case coe v0 of
      C_heap'45'loc_54 v1 v2
        -> coe
             C_heap'45'loc_54 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.offsetHL
d_offsetHL_124 :: T_HeapLocation_44 -> Integer -> T_HeapLocation_44
d_offsetHL_124 v0 v1
  = case coe v0 of
      C_heap'45'loc_54 v2 v3
        -> coe C_heap'45'loc_54 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.sucLoc
d_sucLoc_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_110 -> T_ValueLocation_110
d_sucLoc_134 ~v0 v1 = du_sucLoc_134 v1
du_sucLoc_134 :: T_ValueLocation_110 -> T_ValueLocation_110
du_sucLoc_134 v0
  = case coe v0 of
      C_OnStack_114 v1 v2
        -> coe
             C_OnStack_114 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_OnHeap_116 v1 -> coe C_OnHeap_116 (coe d_sucHL_118 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.offsetLoc
d_offsetLoc_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_110 -> Integer -> T_ValueLocation_110
d_offsetLoc_144 ~v0 v1 v2 = du_offsetLoc_144 v1 v2
du_offsetLoc_144 ::
  T_ValueLocation_110 -> Integer -> T_ValueLocation_110
du_offsetLoc_144 v0 v1
  = case coe v0 of
      C_OnStack_114 v2 v3
        -> coe C_OnStack_114 (coe v2) (coe addInt (coe v1) (coe v3))
      C_OnHeap_116 v2
        -> coe C_OnHeap_116 (coe d_offsetHL_124 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.StackMem
d_StackMem_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_158 = erased
-- Once.CCC.SlotMachine.HeapMem
d_HeapMem_162 :: ()
d_HeapMem_162 = erased
-- Once.CCC.SlotMachine.RegId
d_RegId_164 = ()
data T_RegId_164
  = C_RAX_166 | C_RDI_168 | C_RSI_170 | C_R12_172 | C_R14_174 |
    C_R15_176
-- Once.CCC.SlotMachine._≟R_
d__'8799'R__182 ::
  T_RegId_164 ->
  T_RegId_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__182 v0 v1
  = case coe v0 of
      C_RAX_166
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_RDI_168
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_RSI_170
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_R12_172
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_R14_174
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_R15_176
        -> case coe v1 of
             C_RAX_166
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RDI_168
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_RSI_170
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R12_172
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R14_174
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_R15_176
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers
d_Registers_186 a0 = ()
data T_Registers_186
  = C_mkRegs_214 T_ValueLocation_110 T_ValueLocation_110
                 T_ValueLocation_110 T_ValueLocation_110 T_ValueLocation_110
                 T_ValueLocation_110
-- Once.CCC.SlotMachine.Registers.rax
d_rax_202 :: T_Registers_186 -> T_ValueLocation_110
d_rax_202 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers.rdi
d_rdi_204 :: T_Registers_186 -> T_ValueLocation_110
d_rdi_204 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers.rsi
d_rsi_206 :: T_Registers_186 -> T_ValueLocation_110
d_rsi_206 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers.r12
d_r12_208 :: T_Registers_186 -> T_ValueLocation_110
d_r12_208 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers.r14
d_r14_210 :: T_Registers_186 -> T_ValueLocation_110
d_r14_210 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Registers.r15
d_r15_212 :: T_Registers_186 -> T_ValueLocation_110
d_r15_212 v0
  = case coe v0 of
      C_mkRegs_214 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.readReg
d_readReg_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_186 -> T_RegId_164 -> T_ValueLocation_110
d_readReg_218 ~v0 v1 v2 = du_readReg_218 v1 v2
du_readReg_218 ::
  T_Registers_186 -> T_RegId_164 -> T_ValueLocation_110
du_readReg_218 v0 v1
  = case coe v1 of
      C_RAX_166 -> coe d_rax_202 (coe v0)
      C_RDI_168 -> coe d_rdi_204 (coe v0)
      C_RSI_170 -> coe d_rsi_206 (coe v0)
      C_R12_172 -> coe d_r12_208 (coe v0)
      C_R14_174 -> coe d_r14_210 (coe v0)
      C_R15_176 -> coe d_r15_212 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.writeReg
d_writeReg_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_186 ->
  T_RegId_164 -> T_ValueLocation_110 -> T_Registers_186
d_writeReg_234 ~v0 v1 v2 = du_writeReg_234 v1 v2
du_writeReg_234 ::
  T_Registers_186 ->
  T_RegId_164 -> T_ValueLocation_110 -> T_Registers_186
du_writeReg_234 v0 v1
  = case coe v1 of
      C_RAX_166
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe v2) (coe d_rdi_204 (coe v0))
                  (coe d_rsi_206 (coe v0)) (coe d_r12_208 (coe v0))
                  (coe d_r14_210 (coe v0)) (coe d_r15_212 (coe v0)))
      C_RDI_168
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe d_rax_202 (coe v0)) (coe v2)
                  (coe d_rsi_206 (coe v0)) (coe d_r12_208 (coe v0))
                  (coe d_r14_210 (coe v0)) (coe d_r15_212 (coe v0)))
      C_RSI_170
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe d_rax_202 (coe v0)) (coe d_rdi_204 (coe v0))
                  (coe v2) (coe d_r12_208 (coe v0)) (coe d_r14_210 (coe v0))
                  (coe d_r15_212 (coe v0)))
      C_R12_172
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe d_rax_202 (coe v0)) (coe d_rdi_204 (coe v0))
                  (coe d_rsi_206 (coe v0)) (coe v2) (coe d_r14_210 (coe v0))
                  (coe d_r15_212 (coe v0)))
      C_R14_174
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe d_rax_202 (coe v0)) (coe d_rdi_204 (coe v0))
                  (coe d_rsi_206 (coe v0)) (coe d_r12_208 (coe v0)) (coe v2)
                  (coe d_r15_212 (coe v0)))
      C_R15_176
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_214 (coe d_rax_202 (coe v0)) (coe d_rdi_204 (coe v0))
                  (coe d_rsi_206 (coe v0)) (coe d_r12_208 (coe v0))
                  (coe d_r14_210 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.writeReg-preserves
d_writeReg'45'preserves_270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_186 ->
  T_RegId_164 ->
  T_RegId_164 ->
  T_ValueLocation_110 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_270 = erased
-- Once.CCC.SlotMachine.writeReg-same
d_writeReg'45'same_520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_186 ->
  T_RegId_164 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_520 = erased
-- Once.CCC.SlotMachine.LocState
d_LocState_548 a0 = ()
data T_LocState_548
  = C_mkLocState_568 T_Registers_186
                     (AgdaAny -> Integer -> Maybe T_ValueLocation_110)
                     (T_HeapLocation_44 -> Maybe T_HeapLocation_44) Bool
-- Once.CCC.SlotMachine.LocState.regs
d_regs_560 :: T_LocState_548 -> T_Registers_186
d_regs_560 v0
  = case coe v0 of
      C_mkLocState_568 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.LocState.stackMem
d_stackMem_562 ::
  T_LocState_548 -> AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_stackMem_562 v0
  = case coe v0 of
      C_mkLocState_568 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.LocState.heapMem
d_heapMem_564 ::
  T_LocState_548 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_heapMem_564 v0
  = case coe v0 of
      C_mkLocState_568 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.LocState.halted
d_halted_566 :: T_LocState_548 -> Bool
d_halted_566 v0
  = case coe v0 of
      C_mkLocState_568 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.MemOps.readStackLoc
d_readStackLoc_598 ::
  T_LocState_548 -> AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_readStackLoc_598 v0 v1 v2 = coe d_stackMem_562 v0 v1 v2
-- Once.CCC.SlotMachine.MemOps.readHeapLoc
d_readHeapLoc_606 ::
  T_LocState_548 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_readHeapLoc_606 v0 v1 = coe d_heapMem_564 v0 v1
-- Once.CCC.SlotMachine.MemOps.readLoc
d_readLoc_612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
d_readLoc_612 ~v0 v1 v2 = du_readLoc_612 v1 v2
du_readLoc_612 ::
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
du_readLoc_612 v0 v1
  = case coe v1 of
      C_OnStack_114 v2 v3 -> coe d_stackMem_562 v0 v2 v3
      C_OnHeap_116 v2
        -> let v3 = coe d_heapMem_564 v0 v2 in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_OnHeap_116 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.MemOps.writeStackMem
d_writeStackMem_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_110) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_110 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_writeStackMem_638 v0 v1 v2 v3 v4 v5 v6
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
-- Once.CCC.SlotMachine.MemOps.writeHeapMem
d_writeHeapMem_680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_writeHeapMem_680 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_680 v1 v2 v3 v4
du_writeHeapMem_680 ::
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
du_writeHeapMem_680 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v4 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_heap'45'offset_52 (coe v1)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_heap'45'offset_52 (coe v1))
                    (coe d_heap'45'offset_52 (coe v3)))) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v5 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe d_ref'45'id_14 (coe d_heap'45'ref_50 (coe v1))))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe d_ref'45'id_14 (coe d_heap'45'ref_50 (coe v1)))
                       (coe d_ref'45'id_14 (coe d_heap'45'ref_50 (coe v3))))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe d_ref'45'id_14 (coe d_heap'45'ref_50 (coe v1)))
                          (coe d_ref'45'id_14 (coe d_heap'45'ref_50 (coe v3)))))) in
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
-- Once.CCC.SlotMachine.MemOps.writeLocToStack
d_writeLocToStack_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  AgdaAny -> Integer -> T_ValueLocation_110 -> T_LocState_548
d_writeLocToStack_710 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_568 (coe d_regs_560 (coe v1))
      (coe
         d_writeStackMem_638 (coe v0) (coe d_stackMem_562 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_564 (coe v1)) (coe d_halted_566 (coe v1))
-- Once.CCC.SlotMachine.MemOps.writeLocToHeap
d_writeLocToHeap_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
d_writeLocToHeap_720 ~v0 v1 v2 v3 = du_writeLocToHeap_720 v1 v2 v3
du_writeLocToHeap_720 ::
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
du_writeLocToHeap_720 v0 v1 v2
  = coe
      C_mkLocState_568 (coe d_regs_560 (coe v0))
      (coe d_stackMem_562 (coe v0))
      (coe
         du_writeHeapMem_680 (coe d_heapMem_564 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_566 (coe v0))
-- Once.CCC.SlotMachine.MemOps.writeLoc
d_writeLoc_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_ValueLocation_110 -> T_ValueLocation_110 -> T_LocState_548
d_writeLoc_728 v0 v1 v2 v3
  = case coe v2 of
      C_OnStack_114 v4 v5
        -> coe
             d_writeLocToStack_710 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_OnHeap_116 v4
        -> case coe v3 of
             C_OnStack_114 v5 v6 -> coe v1
             C_OnHeap_116 v5
               -> coe du_writeLocToHeap_720 (coe v1) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.LocSourceExt
d_LocSourceExt_750 a0 = ()
data T_LocSourceExt_750
  = C_Loc_754 T_ValueLocation_110 | C_IndReg_756 T_RegId_164 |
    C_IndRegSuc_758 T_RegId_164
-- Once.CCC.SlotMachine.resolveSourceExt
d_resolveSourceExt_762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_186 -> T_LocSourceExt_750 -> T_ValueLocation_110
d_resolveSourceExt_762 ~v0 v1 v2 = du_resolveSourceExt_762 v1 v2
du_resolveSourceExt_762 ::
  T_Registers_186 -> T_LocSourceExt_750 -> T_ValueLocation_110
du_resolveSourceExt_762 v0 v1
  = case coe v1 of
      C_Loc_754 v2 -> coe v2
      C_IndReg_756 v2 -> coe du_readReg_218 (coe v0) (coe v2)
      C_IndRegSuc_758 v2
        -> coe du_sucLoc_134 (coe du_readReg_218 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.Instr
d_Instr_778 a0 = ()
data T_Instr_778
  = C_load_782 T_RegId_164 T_LocSourceExt_750 |
    C_store_784 T_LocSourceExt_750 T_RegId_164 |
    C_mov_786 T_RegId_164 T_RegId_164
-- Once.CCC.SlotMachine.ExecFinal._.readHeapLoc
d_readHeapLoc_794 ::
  T_LocState_548 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_readHeapLoc_794 v0 v1 = coe d_heapMem_564 v0 v1
-- Once.CCC.SlotMachine.ExecFinal._.readLoc
d_readLoc_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
d_readLoc_796 ~v0 = du_readLoc_796
du_readLoc_796 ::
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
du_readLoc_796 = coe du_readLoc_612
-- Once.CCC.SlotMachine.ExecFinal._.readStackLoc
d_readStackLoc_798 ::
  T_LocState_548 -> AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_readStackLoc_798 v0 v1 v2 = coe d_stackMem_562 v0 v1 v2
-- Once.CCC.SlotMachine.ExecFinal._.writeHeapMem
d_writeHeapMem_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_writeHeapMem_800 ~v0 = du_writeHeapMem_800
du_writeHeapMem_800 ::
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
du_writeHeapMem_800 = coe du_writeHeapMem_680
-- Once.CCC.SlotMachine.ExecFinal._.writeLoc
d_writeLoc_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_ValueLocation_110 -> T_ValueLocation_110 -> T_LocState_548
d_writeLoc_802 v0 = coe d_writeLoc_728 (coe v0)
-- Once.CCC.SlotMachine.ExecFinal._.writeLocToHeap
d_writeLocToHeap_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
d_writeLocToHeap_804 ~v0 = du_writeLocToHeap_804
du_writeLocToHeap_804 ::
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
du_writeLocToHeap_804 = coe du_writeLocToHeap_720
-- Once.CCC.SlotMachine.ExecFinal._.writeLocToStack
d_writeLocToStack_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  AgdaAny -> Integer -> T_ValueLocation_110 -> T_LocState_548
d_writeLocToStack_806 v0 = coe d_writeLocToStack_710 (coe v0)
-- Once.CCC.SlotMachine.ExecFinal._.writeStackMem
d_writeStackMem_808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_110) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_110 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_writeStackMem_808 v0 = coe d_writeStackMem_638 (coe v0)
-- Once.CCC.SlotMachine.ExecFinal.exec
d_exec_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_778 -> T_LocState_548 -> T_LocState_548
d_exec_810 v0 v1
  = case coe v1 of
      C_load_782 v2 v3
        -> coe
             (\ v4 ->
                let v5
                      = coe
                          du_readLoc_612 (coe v4)
                          (coe du_resolveSourceExt_762 (coe d_regs_560 (coe v4)) (coe v3)) in
                coe
                  (case coe v5 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                       -> coe
                            C_mkLocState_568 (coe du_writeReg_234 (d_regs_560 (coe v4)) v2 v6)
                            (coe d_stackMem_562 (coe v4)) (coe d_heapMem_564 (coe v4))
                            (coe d_halted_566 (coe v4))
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            C_mkLocState_568 (coe d_regs_560 (coe v4))
                            (coe d_stackMem_562 (coe v4)) (coe d_heapMem_564 (coe v4))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     _ -> MAlonzo.RTE.mazUnreachableError))
      C_store_784 v2 v3
        -> coe
             (\ v4 ->
                d_writeLoc_728
                  (coe v0) (coe v4)
                  (coe du_resolveSourceExt_762 (coe d_regs_560 (coe v4)) (coe v2))
                  (coe du_readReg_218 (coe d_regs_560 (coe v4)) (coe v3)))
      C_mov_786 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_568
                  (coe
                     du_writeReg_234 (d_regs_560 (coe v4)) v2
                     (coe du_readReg_218 (coe d_regs_560 (coe v4)) (coe v3)))
                  (coe d_stackMem_562 (coe v4)) (coe d_heapMem_564 (coe v4))
                  (coe d_halted_566 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.ExecFinal.execList
d_execList_852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_778] -> T_LocState_548 -> T_LocState_548
d_execList_852 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_566 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_852 (coe v0) (coe v4) (coe d_exec_810 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.SlotMachine.ExecLemmas._.readHeapLoc
d_readHeapLoc_884 ::
  T_LocState_548 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_readHeapLoc_884 v0 v1 = coe d_heapMem_564 v0 v1
-- Once.CCC.SlotMachine.ExecLemmas._.readLoc
d_readLoc_886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
d_readLoc_886 ~v0 = du_readLoc_886
du_readLoc_886 ::
  T_LocState_548 -> T_ValueLocation_110 -> Maybe T_ValueLocation_110
du_readLoc_886 = coe du_readLoc_612
-- Once.CCC.SlotMachine.ExecLemmas._.readStackLoc
d_readStackLoc_888 ::
  T_LocState_548 -> AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_readStackLoc_888 v0 v1 v2 = coe d_stackMem_562 v0 v1 v2
-- Once.CCC.SlotMachine.ExecLemmas._.writeHeapMem
d_writeHeapMem_890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
d_writeHeapMem_890 ~v0 = du_writeHeapMem_890
du_writeHeapMem_890 ::
  (T_HeapLocation_44 -> Maybe T_HeapLocation_44) ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> Maybe T_HeapLocation_44
du_writeHeapMem_890 = coe du_writeHeapMem_680
-- Once.CCC.SlotMachine.ExecLemmas._.writeLoc
d_writeLoc_892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_ValueLocation_110 -> T_ValueLocation_110 -> T_LocState_548
d_writeLoc_892 v0 = coe d_writeLoc_728 (coe v0)
-- Once.CCC.SlotMachine.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
d_writeLocToHeap_894 ~v0 = du_writeLocToHeap_894
du_writeLocToHeap_894 ::
  T_LocState_548 ->
  T_HeapLocation_44 -> T_HeapLocation_44 -> T_LocState_548
du_writeLocToHeap_894 = coe du_writeLocToHeap_720
-- Once.CCC.SlotMachine.ExecLemmas._.writeLocToStack
d_writeLocToStack_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  AgdaAny -> Integer -> T_ValueLocation_110 -> T_LocState_548
d_writeLocToStack_896 v0 = coe d_writeLocToStack_710 (coe v0)
-- Once.CCC.SlotMachine.ExecLemmas._.writeStackMem
d_writeStackMem_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_ValueLocation_110) ->
  AgdaAny ->
  Integer ->
  T_ValueLocation_110 ->
  AgdaAny -> Integer -> Maybe T_ValueLocation_110
d_writeStackMem_898 v0 = coe d_writeStackMem_638 (coe v0)
-- Once.CCC.SlotMachine.ExecLemmas._.exec
d_exec_902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_778 -> T_LocState_548 -> T_LocState_548
d_exec_902 v0 = coe d_exec_810 (coe v0)
-- Once.CCC.SlotMachine.ExecLemmas._.execList
d_execList_904 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_778] -> T_LocState_548 -> T_LocState_548
d_execList_904 v0 = coe d_execList_852 (coe v0)
-- Once.CCC.SlotMachine.ExecLemmas.load-result
d_load'45'result_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_914 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 ->
  T_RegId_164 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_952 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-failed-preserves
d_load'45'failed'45'preserves_994 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'preserves_994 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1022 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1052 = erased
-- Once.CCC.SlotMachine.ExecLemmas.mov-result
d_mov'45'result_1082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_RegId_164 ->
  T_LocState_548 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1082 = erased
-- Once.CCC.SlotMachine.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_RegId_164 ->
  T_LocState_548 ->
  T_RegId_164 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1098 = erased
-- Once.CCC.SlotMachine.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_RegId_164 ->
  T_LocState_548 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1116 = erased
-- Once.CCC.SlotMachine.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_RegId_164 ->
  T_LocState_548 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1130 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1146 = erased
-- Once.CCC.SlotMachine.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegId_164 ->
  T_LocSourceExt_750 ->
  T_LocState_548 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1180 = erased
-- Once.CCC.SlotMachine.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_LocState_548 ->
  T_ValueLocation_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1200 = erased
-- Once.CCC.SlotMachine.ExecLemmas._.just-injective
d_just'45'injective_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_548 ->
  T_LocState_548 ->
  T_HeapLocation_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_HeapLocation_44 ->
  T_HeapLocation_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injective_1258 = erased
