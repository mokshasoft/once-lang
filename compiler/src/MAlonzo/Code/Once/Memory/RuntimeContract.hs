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

module MAlonzo.Code.Once.Memory.RuntimeContract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics

-- Once.Memory.RuntimeContract.RuntimeContract
d_RuntimeContract_6 = ()
data T_RuntimeContract_6
  = C_constructor_90 Integer Integer Integer Integer Integer
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Memory.RuntimeContract.RuntimeContract.stack-upper
d_stack'45'upper_26 :: T_RuntimeContract_6 -> Integer
d_stack'45'upper_26 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-lower
d_heap'45'lower_28 :: T_RuntimeContract_6 -> Integer
d_heap'45'lower_28 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-upper
d_heap'45'upper_30 :: T_RuntimeContract_6 -> Integer
d_heap'45'upper_30 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.code-lower
d_code'45'lower_32 :: T_RuntimeContract_6 -> Integer
d_code'45'lower_32 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.code-upper
d_code'45'upper_34 :: T_RuntimeContract_6 -> Integer
d_code'45'upper_34 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.stack<heap
d_stack'60'heap_36 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'60'heap_36 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-valid
d_heap'45'valid_38 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'valid_38 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap<code
d_heap'60'code_40 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'60'code_40 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.code-valid
d_code'45'valid_42 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_code'45'valid_42 v0
  = case coe v0 of
      C_constructor_90 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.stack-bounds
d_stack'45'bounds_44 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_44 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe (0 :: Integer)) (coe d_stack'45'upper_26 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Memory.RuntimeContract.RuntimeContract.heap-bounds
d_heap'45'bounds_46 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_46 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe d_heap'45'lower_28 (coe v0)) (coe d_heap'45'upper_30 (coe v0))
      (coe d_heap'45'valid_38 (coe v0))
-- Once.Memory.RuntimeContract.RuntimeContract.code-bounds
d_code'45'bounds_48 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_48 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe d_code'45'lower_32 (coe v0)) (coe d_code'45'upper_34 (coe v0))
      (coe d_code'45'valid_42 (coe v0))
-- Once.Memory.RuntimeContract.RuntimeContract.gap
d_gap_56 ::
  T_RuntimeContract_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_gap_56 = erased
-- Once.Memory.RuntimeContract.RuntimeContract.stack<code
d_stack'60'code_64 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'60'code_64 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe d_heap'45'lower_28 (coe v0)) (coe d_stack'60'heap_36 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
         (coe d_heap'45'valid_38 (coe v0)) (coe d_heap'60'code_40 (coe v0)))
-- Once.Memory.RuntimeContract.RuntimeContract.intervals-disjoint
d_intervals'45'disjoint_68 ::
  T_RuntimeContract_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_68 ~v0 ~v1 = du_intervals'45'disjoint_68
du_intervals'45'disjoint_68 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_intervals'45'disjoint_68
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
