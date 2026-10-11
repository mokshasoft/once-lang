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

module MAlonzo.Code.Once.Memory.HeapAddress where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Memory.HeapAddress.HeapOffset
d_HeapOffset_6 :: ()
d_HeapOffset_6 = erased
-- Once.Memory.HeapAddress.HeapRef
d_HeapRef_8 = ()
newtype T_HeapRef_8 = C_mkHeapRef_14 Integer
-- Once.Memory.HeapAddress.HeapRef.ref-id
d_ref'45'id_12 :: T_HeapRef_8 -> Integer
d_ref'45'id_12 v0
  = case coe v0 of
      C_mkHeapRef_14 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.HeapAddress._≟H_
d__'8799'H__16 ::
  T_HeapRef_8 ->
  T_HeapRef_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'H__16 v0 v1
  = case coe v0 of
      C_mkHeapRef_14 v2
        -> case coe v1 of
             C_mkHeapRef_14 v3
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
-- Once.Memory.HeapAddress.HeapLocation
d_HeapLocation_38 = ()
data T_HeapLocation_38 = C_heap'45'loc_48 T_HeapRef_8 Integer
-- Once.Memory.HeapAddress.HeapLocation.heap-ref
d_heap'45'ref_44 :: T_HeapLocation_38 -> T_HeapRef_8
d_heap'45'ref_44 v0
  = case coe v0 of
      C_heap'45'loc_48 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.HeapAddress.HeapLocation.heap-offset
d_heap'45'offset_46 :: T_HeapLocation_38 -> Integer
d_heap'45'offset_46 v0
  = case coe v0 of
      C_heap'45'loc_48 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.HeapAddress.≟HL-aux
d_'8799'HL'45'aux_58 ::
  T_HeapRef_8 ->
  T_HeapRef_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'HL'45'aux_58 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'HL'45'aux_58 v4 v5
du_'8799'HL'45'aux_58 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'HL'45'aux_58 v0 v1
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
-- Once.Memory.HeapAddress._≟HL_
d__'8799'HL__72 ::
  T_HeapLocation_38 ->
  T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'HL__72 v0 v1
  = case coe v0 of
      C_heap'45'loc_48 v2 v3
        -> case coe v1 of
             C_heap'45'loc_48 v4 v5
               -> coe
                    du_'8799'HL'45'aux_58 (coe d__'8799'H__16 (coe v2) (coe v4))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.HeapAddress.hl-ref
d_hl'45'ref_82 :: T_HeapLocation_38 -> T_HeapRef_8
d_hl'45'ref_82 v0 = coe d_heap'45'ref_44 (coe v0)
-- Once.Memory.HeapAddress.sucHL
d_sucHL_84 :: T_HeapLocation_38 -> T_HeapLocation_38
d_sucHL_84 v0
  = case coe v0 of
      C_heap'45'loc_48 v1 v2
        -> coe
             C_heap'45'loc_48 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.HeapAddress.offsetHL
d_offsetHL_90 :: T_HeapLocation_38 -> Integer -> T_HeapLocation_38
d_offsetHL_90 v0 v1
  = case coe v0 of
      C_heap'45'loc_48 v2 v3
        -> coe C_heap'45'loc_48 (coe v2) (coe addInt (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
