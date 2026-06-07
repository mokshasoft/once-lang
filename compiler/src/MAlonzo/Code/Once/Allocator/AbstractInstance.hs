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

module MAlonzo.Code.Once.Allocator.AbstractInstance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Allocator.Interface
import qualified MAlonzo.Code.Once.Memory.HeapAddress

-- Once.Allocator.AbstractInstance.hl-slot-at
d_hl'45'slot'45'at_6 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_hl'45'slot'45'at_6 v0 v1
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_98 (coe v0)
      (coe v1)
-- Once.Allocator.AbstractInstance.State
d_State_12 :: ()
d_State_12 = erased
-- Once.Allocator.AbstractInstance.initial
d_initial_14 :: Integer
d_initial_14 = coe (0 :: Integer)
-- Once.Allocator.AbstractInstance.Allocated
d_Allocated_22 a0 a1 a2 = ()
data T_Allocated_22
  = C_mkAllocated_42 Integer MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Allocator.AbstractInstance.Allocated.ref
d_ref_36 :: T_Allocated_22 -> Integer
d_ref_36 v0
  = case coe v0 of
      C_mkAllocated_42 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.AbstractInstance.Allocated.addr-eq
d_addr'45'eq_38 ::
  T_Allocated_22 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_38 = erased
-- Once.Allocator.AbstractInstance.Allocated.ref<state
d_ref'60'state_40 ::
  T_Allocated_22 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ref'60'state_40 v0
  = case coe v0 of
      C_mkAllocated_42 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.AbstractInstance.alloc-impl
d_alloc'45'impl_52 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alloc'45'impl_52 ~v0 v1 = du_alloc'45'impl_52 v1
du_alloc'45'impl_52 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alloc'45'impl_52 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14 (coe v0))
         (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            C_mkAllocated_42 v0
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                  (coe v0)))))
-- Once.Allocator.AbstractInstance.block-in-region-impl
d_block'45'in'45'region'45'impl_66 ::
  T_Allocated_22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_block'45'in'45'region'45'impl_66 ~v0 ~v1 ~v2
  = du_block'45'in'45'region'45'impl_66
du_block'45'in'45'region'45'impl_66 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_block'45'in'45'region'45'impl_66
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Once.Allocator.AbstractInstance.blocks-disjoint-impl
d_blocks'45'disjoint'45'impl_84 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  Integer ->
  T_Allocated_22 ->
  T_Allocated_22 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_blocks'45'disjoint'45'impl_84 = erased
-- Once.Allocator.AbstractInstance.free-impl
d_free'45'impl_100 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer -> Integer
d_free'45'impl_100 ~v0 v1 = du_free'45'impl_100 v1
du_free'45'impl_100 :: Integer -> Integer
du_free'45'impl_100 v0 = coe v0
-- Once.Allocator.AbstractInstance.alloc-fresh-impl
d_alloc'45'fresh'45'impl_112 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  T_Allocated_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_alloc'45'fresh'45'impl_112 = erased
-- Once.Allocator.AbstractInstance.abstract-allocator
d_abstract'45'allocator_124 ::
  MAlonzo.Code.Once.Allocator.Interface.T_AllocatorInterface_12
d_abstract'45'allocator_124
  = coe
      MAlonzo.Code.Once.Allocator.Interface.C_constructor_132
      d_initial_14 (\ v0 v1 -> coe du_alloc'45'impl_52 v1)
      (\ v0 v1 -> v1)
      (\ v0 v1 v2 v3 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Allocator.AbstractInstance.fresh-loc-disjoint
d_fresh'45'loc'45'disjoint_138 ::
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'loc'45'disjoint_138 = erased
-- Once.Allocator.AbstractInstance.fresh-cell-disjoint
d_fresh'45'cell'45'disjoint_158 ::
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'cell'45'disjoint_158 = erased
