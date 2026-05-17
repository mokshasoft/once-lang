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

module MAlonzo.Code.Once.Memory.MemoryLayoutSemantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Memory.MemoryLayoutSemantics.Addr
d_Addr_6 :: ()
d_Addr_6 = erased
-- Once.Memory.MemoryLayoutSemantics.RegionBounds
d_RegionBounds_8 = ()
data T_RegionBounds_8
  = C_constructor_22 Integer Integer
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Memory.MemoryLayoutSemantics.RegionBounds.lower
d_lower_16 :: T_RegionBounds_8 -> Integer
d_lower_16 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.RegionBounds.upper
d_upper_18 :: T_RegionBounds_8 -> Integer
d_upper_18 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.RegionBounds.bounds-valid
d_bounds'45'valid_20 ::
  T_RegionBounds_8 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bounds'45'valid_20 v0
  = case coe v0 of
      C_constructor_22 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.InRegion
d_InRegion_24 :: T_RegionBounds_8 -> Integer -> ()
d_InRegion_24 = erased
-- Once.Memory.MemoryLayoutSemantics.MemoryLayout
d_MemoryLayout_30 = ()
data T_MemoryLayout_30
  = C_constructor_52 T_RegionBounds_8 T_RegionBounds_8
                     T_RegionBounds_8
                     (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Memory.MemoryLayoutSemantics.MemoryLayout.stack-bounds
d_stack'45'bounds_42 :: T_MemoryLayout_30 -> T_RegionBounds_8
d_stack'45'bounds_42 v0
  = case coe v0 of
      C_constructor_52 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.MemoryLayout.heap-bounds
d_heap'45'bounds_44 :: T_MemoryLayout_30 -> T_RegionBounds_8
d_heap'45'bounds_44 v0
  = case coe v0 of
      C_constructor_52 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.MemoryLayout.code-bounds
d_code'45'bounds_46 :: T_MemoryLayout_30 -> T_RegionBounds_8
d_code'45'bounds_46 v0
  = case coe v0 of
      C_constructor_52 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.MemoryLayout.intervals-disjoint
d_intervals'45'disjoint_50 ::
  T_MemoryLayout_30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_50 v0
  = case coe v0 of
      C_constructor_52 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.StackGrowth
d_StackGrowth_54 = ()
data T_StackGrowth_54
  = C_constructor_140 (Integer -> Integer -> Integer)
                      (Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer -> Integer -> Integer -> AgdaAny -> AgdaAny)
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.grow
d_grow_98 :: T_StackGrowth_54 -> Integer -> Integer -> Integer
d_grow_98 v0
  = case coe v0 of
      C_constructor_140 v1 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.grow-identity
d_grow'45'identity_102 ::
  T_StackGrowth_54 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_grow'45'identity_102 = erased
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.grow-injective
d_grow'45'injective_110 ::
  T_StackGrowth_54 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'injective_110 = erased
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.grow-addr-injective
d_grow'45'addr'45'injective_118 ::
  T_StackGrowth_54 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'addr'45'injective_118 = erased
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.FramePreserved
d_FramePreserved_120 ::
  T_StackGrowth_54 -> Integer -> Integer -> ()
d_FramePreserved_120 = erased
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.StackGrew
d_StackGrew_122 :: T_StackGrowth_54 -> Integer -> Integer -> ()
d_StackGrew_122 = erased
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.frame-preserved-under-growth
d_frame'45'preserved'45'under'45'growth_130 ::
  T_StackGrowth_54 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_frame'45'preserved'45'under'45'growth_130 v0
  = case coe v0 of
      C_constructor_140 v1 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.MemoryLayoutSemantics.StackGrowth.slot-in-preserved-frame
d_slot'45'in'45'preserved'45'frame_138 ::
  T_StackGrowth_54 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_slot'45'in'45'preserved'45'frame_138 v0
  = case coe v0 of
      C_constructor_140 v1 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
