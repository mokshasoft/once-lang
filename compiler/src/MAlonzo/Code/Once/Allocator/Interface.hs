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
  = C_constructor_108 AgdaAny
                      (Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      (AgdaAny ->
                       AgdaAny ->
                       Integer ->
                       AgdaAny ->
                       Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
-- Once.Allocator.Interface.AllocatorInterface.State
d_State_64 :: T_AllocatorInterface_12 -> ()
d_State_64 = erased
-- Once.Allocator.Interface.AllocatorInterface.init
d_init_66 :: T_AllocatorInterface_12 -> AgdaAny
d_init_66 v0
  = case coe v0 of
      C_constructor_108 v2 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.Allocated
d_Allocated_68 ::
  T_AllocatorInterface_12 -> AgdaAny -> AgdaAny -> Integer -> ()
d_Allocated_68 = erased
-- Once.Allocator.Interface.AllocatorInterface.alloc
d_alloc_78 ::
  T_AllocatorInterface_12 ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alloc_78 v0
  = case coe v0 of
      C_constructor_108 v2 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.block-in-region
d_block'45'in'45'region_88 ::
  T_AllocatorInterface_12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_block'45'in'45'region_88 v0
  = case coe v0 of
      C_constructor_108 v2 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Allocator.Interface.AllocatorInterface.blocks-disjoint
d_blocks'45'disjoint_106 ::
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
d_blocks'45'disjoint_106 = erased
