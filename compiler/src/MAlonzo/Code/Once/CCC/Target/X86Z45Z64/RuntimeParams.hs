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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics
import qualified MAlonzo.Code.Once.Memory.RuntimeContract

-- Once.CCC.Target.X86-64.RuntimeParams.x86-64-runtime
d_x86'45'64'45'runtime_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-64.RuntimeParams.x86-64-runtime"
-- Once.CCC.Target.X86-64.RuntimeParams._.code-bounds
d_code'45'bounds_14 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_14
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'bounds_46
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.code-upper
d_code'45'upper_16 :: Integer
d_code'45'upper_16
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'upper_38
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.heap-bounds
d_heap'45'bounds_18 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_18
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'bounds_44
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.heap-lower
d_heap'45'lower_20 :: Integer
d_heap'45'lower_20
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'lower_34
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.heap-upper
d_heap'45'upper_22 :: Integer
d_heap'45'upper_22
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'upper_36
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.heap-valid
d_heap'45'valid_24 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'valid_24
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'valid_40
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.intervals-disjoint
d_intervals'45'disjoint_26 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_26
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_intervals'45'disjoint_50
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.prog-fits
d_prog'45'fits_28 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prog'45'fits_28
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_prog'45'fits_54
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.stack-bounds
d_stack'45'bounds_30 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_30
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'45'bounds_42
      (coe d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.RuntimeParams._.stack-upper
d_stack'45'upper_32 :: Integer
d_stack'45'upper_32
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'45'upper_32
      (coe d_x86'45'64'45'runtime_10)
