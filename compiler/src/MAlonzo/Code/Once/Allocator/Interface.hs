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

module MAlonzo.Code.Once.Allocator.Interface where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Allocator.Interface.AllocatorInterface
d_AllocatorInterface_12 a0 a1 a2 = ()
data T_AllocatorInterface_12
  = C_constructor_132 AgdaAny
                      (Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny ->
                       AgdaAny ->
                       Integer ->
                       AgdaAny ->
                       Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
-- Once.Allocator.Interface.AllocatorInterface.State
d_State_76 :: T_AllocatorInterface_12 -> ()
d_State_76 = erased
-- Once.Allocator.Interface.AllocatorInterface.init
d_init_78 :: T_AllocatorInterface_12 -> AgdaAny
d_init_78 v0
  = case coe v0 of
      C_constructor_132 v2 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.Allocated
d_Allocated_80 ::
  T_AllocatorInterface_12 -> AgdaAny -> AgdaAny -> Integer -> ()
d_Allocated_80 = erased
-- Once.Allocator.Interface.AllocatorInterface.alloc
d_alloc_90 ::
  T_AllocatorInterface_12 ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alloc_90 v0
  = case coe v0 of
      C_constructor_132 v2 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.free
d_free_92 ::
  T_AllocatorInterface_12 -> AgdaAny -> AgdaAny -> AgdaAny
d_free_92 v0
  = case coe v0 of
      C_constructor_132 v2 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.block-in-region
d_block'45'in'45'region_102 ::
  T_AllocatorInterface_12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_block'45'in'45'region_102 v0
  = case coe v0 of
      C_constructor_132 v2 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.blocks-disjoint
d_blocks'45'disjoint_120 ::
  T_AllocatorInterface_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_blocks'45'disjoint_120 = erased
-- Once.Allocator.Interface.AllocatorInterface.alloc-fresh
d_alloc'45'fresh_130 ::
  T_AllocatorInterface_12 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_alloc'45'fresh_130 = erased
