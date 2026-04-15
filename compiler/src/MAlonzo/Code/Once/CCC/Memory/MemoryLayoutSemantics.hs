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

module MAlonzo.Code.Once.CCC.Memory.MemoryLayoutSemantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.CCC.Memory.MemoryLayoutSemantics.Addr
d_Addr_8 :: ()
d_Addr_8 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.RegionBounds
d_RegionBounds_10 = ()
data T_RegionBounds_10
  = C_constructor_24 Integer Integer
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Memory.MemoryLayoutSemantics.RegionBounds.lower
d_lower_18 :: T_RegionBounds_10 -> Integer
d_lower_18 v0
  = case coe v0 of
      C_constructor_24 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.RegionBounds.upper
d_upper_20 :: T_RegionBounds_10 -> Integer
d_upper_20 v0
  = case coe v0 of
      C_constructor_24 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.RegionBounds.bounds-valid
d_bounds'45'valid_22 ::
  T_RegionBounds_10 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bounds'45'valid_22 v0
  = case coe v0 of
      C_constructor_24 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.InRegion
d_InRegion_26 :: T_RegionBounds_10 -> Integer -> ()
d_InRegion_26 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.MemoryLayout
d_MemoryLayout_32 = ()
data T_MemoryLayout_32
  = C_constructor_54 T_RegionBounds_10 T_RegionBounds_10
                     T_RegionBounds_10
                     (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Memory.MemoryLayoutSemantics.MemoryLayout.stack-bounds
d_stack'45'bounds_44 :: T_MemoryLayout_32 -> T_RegionBounds_10
d_stack'45'bounds_44 v0
  = case coe v0 of
      C_constructor_54 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.MemoryLayout.heap-bounds
d_heap'45'bounds_46 :: T_MemoryLayout_32 -> T_RegionBounds_10
d_heap'45'bounds_46 v0
  = case coe v0 of
      C_constructor_54 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.MemoryLayout.code-bounds
d_code'45'bounds_48 :: T_MemoryLayout_32 -> T_RegionBounds_10
d_code'45'bounds_48 v0
  = case coe v0 of
      C_constructor_54 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.MemoryLayout.intervals-disjoint
d_intervals'45'disjoint_52 ::
  T_MemoryLayout_32 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_52 v0
  = case coe v0 of
      C_constructor_54 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth
d_StackGrowth_56 = ()
data T_StackGrowth_56
  = C_constructor_142 (Integer -> Integer -> Integer)
                      (Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer -> Integer -> Integer -> AgdaAny -> AgdaAny)
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.grow
d_grow_100 :: T_StackGrowth_56 -> Integer -> Integer -> Integer
d_grow_100 v0
  = case coe v0 of
      C_constructor_142 v1 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.grow-identity
d_grow'45'identity_104 ::
  T_StackGrowth_56 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_grow'45'identity_104 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.grow-injective
d_grow'45'injective_112 ::
  T_StackGrowth_56 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'injective_112 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.grow-addr-injective
d_grow'45'addr'45'injective_120 ::
  T_StackGrowth_56 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'addr'45'injective_120 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.FramePreserved
d_FramePreserved_122 ::
  T_StackGrowth_56 -> Integer -> Integer -> ()
d_FramePreserved_122 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.StackGrew
d_StackGrew_124 :: T_StackGrowth_56 -> Integer -> Integer -> ()
d_StackGrew_124 = erased
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.frame-preserved-under-growth
d_frame'45'preserved'45'under'45'growth_132 ::
  T_StackGrowth_56 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_frame'45'preserved'45'under'45'growth_132 v0
  = case coe v0 of
      C_constructor_142 v1 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Memory.MemoryLayoutSemantics.StackGrowth.slot-in-preserved-frame
d_slot'45'in'45'preserved'45'frame_140 ::
  T_StackGrowth_56 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_slot'45'in'45'preserved'45'frame_140 v0
  = case coe v0 of
      C_constructor_142 v1 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
