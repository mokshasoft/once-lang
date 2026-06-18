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

module MAlonzo.Code.Once.Memory.Regions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics

-- Once.Memory.Regions.stack-bounds
d_stack'45'bounds_8 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_8 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_stack'45'bounds_42
      (coe v0)
-- Once.Memory.Regions.heap-bounds
d_heap'45'bounds_10 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_10 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_heap'45'bounds_44
      (coe v0)
-- Once.Memory.Regions.code-bounds
d_code'45'bounds_12 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_12 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_code'45'bounds_46
      (coe v0)
-- Once.Memory.Regions.InStack
d_InStack_14 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer -> ()
d_InStack_14 = erased
-- Once.Memory.Regions.InHeap
d_InHeap_18 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer -> ()
d_InHeap_18 = erased
-- Once.Memory.Regions.InCode
d_InCode_22 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer -> ()
d_InCode_22 = erased
-- Once.Memory.Regions.intervals-disjoint
d_intervals'45'disjoint_28 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_28 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_intervals'45'disjoint_50
      (coe v0)
-- Once.Memory.Regions.stack-heap-disjoint
d_stack'45'heap'45'disjoint_32 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'heap'45'disjoint_32 = erased
-- Once.Memory.Regions.stack-code-disjoint
d_stack'45'code'45'disjoint_42 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'code'45'disjoint_42 = erased
-- Once.Memory.Regions.heap-code-disjoint
d_heap'45'code'45'disjoint_52 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'45'code'45'disjoint_52 = erased
-- Once.Memory.Regions.stack-heap-addr-disjoint
d_stack'45'heap'45'addr'45'disjoint_64 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'heap'45'addr'45'disjoint_64 = erased
-- Once.Memory.Regions.stack-code-addr-disjoint
d_stack'45'code'45'addr'45'disjoint_80 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'code'45'addr'45'disjoint_80 = erased
-- Once.Memory.Regions.heap-code-addr-disjoint
d_heap'45'code'45'addr'45'disjoint_96 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'45'code'45'addr'45'disjoint_96 = erased
-- Once.Memory.Regions.HeapAddr
d_HeapAddr_108 a0 = ()
data T_HeapAddr_108
  = C_heap'45'addr_118 Integer MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Memory.Regions.HeapAddr.haddr
d_haddr_114 :: T_HeapAddr_108 -> Integer
d_haddr_114 v0
  = case coe v0 of
      C_heap'45'addr_118 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.Regions.HeapAddr.in-heap
d_in'45'heap_116 ::
  T_HeapAddr_108 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'heap_116 v0
  = case coe v0 of
      C_heap'45'addr_118 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.Regions.HeapPointer
d_HeapPointer_120 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  ()
d_HeapPointer_120 = erased
