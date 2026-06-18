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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics

-- Once.Memory.RuntimeContract.RuntimeContract
d_RuntimeContract_6 = ()
data T_RuntimeContract_6
  = C_constructor_56 Integer Integer Integer Integer
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                     (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                     (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Memory.RuntimeContract.RuntimeContract.stack-upper
d_stack'45'upper_32 :: T_RuntimeContract_6 -> Integer
d_stack'45'upper_32 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-lower
d_heap'45'lower_34 :: T_RuntimeContract_6 -> Integer
d_heap'45'lower_34 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-upper
d_heap'45'upper_36 :: T_RuntimeContract_6 -> Integer
d_heap'45'upper_36 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.code-upper
d_code'45'upper_38 :: T_RuntimeContract_6 -> Integer
d_code'45'upper_38 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.heap-valid
d_heap'45'valid_40 ::
  T_RuntimeContract_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'valid_40 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.stack-bounds
d_stack'45'bounds_42 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_42 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe (0 :: Integer)) (coe d_stack'45'upper_32 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Memory.RuntimeContract.RuntimeContract.heap-bounds
d_heap'45'bounds_44 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_44 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe d_heap'45'lower_34 (coe v0)) (coe d_heap'45'upper_36 (coe v0))
      (coe d_heap'45'valid_40 (coe v0))
-- Once.Memory.RuntimeContract.RuntimeContract.code-bounds
d_code'45'bounds_46 ::
  T_RuntimeContract_6 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_46 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_22
      (coe (0 :: Integer)) (coe d_code'45'upper_38 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Memory.RuntimeContract.RuntimeContract.intervals-disjoint
d_intervals'45'disjoint_50 ::
  T_RuntimeContract_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_50 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.RuntimeContract.RuntimeContract.prog-fits
d_prog'45'fits_54 ::
  T_RuntimeContract_6 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prog'45'fits_54 v0
  = case coe v0 of
      C_constructor_56 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
