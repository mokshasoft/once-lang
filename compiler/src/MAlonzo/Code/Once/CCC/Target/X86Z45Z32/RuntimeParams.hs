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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.RuntimeParams where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics
import qualified MAlonzo.Code.Once.Memory.RuntimeContract

-- Once.CCC.Target.X86-32.RuntimeParams.x86-32-runtime
d_x86'45'32'45'runtime_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Target.X86-32.RuntimeParams.x86-32-runtime"
-- Once.CCC.Target.X86-32.RuntimeParams._.code-bounds
d_code'45'bounds_14 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_14
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'bounds_48
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.code-lower
d_code'45'lower_16 :: Integer
d_code'45'lower_16
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'lower_32
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.code-upper
d_code'45'upper_18 :: Integer
d_code'45'upper_18
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'upper_34
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.code-valid
d_code'45'valid_20 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_code'45'valid_20
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'valid_42
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.heap-bounds
d_heap'45'bounds_22 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_22
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'bounds_46
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.heap-lower
d_heap'45'lower_24 :: Integer
d_heap'45'lower_24
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'lower_28
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.heap-upper
d_heap'45'upper_26 :: Integer
d_heap'45'upper_26
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'upper_30
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.heap-valid
d_heap'45'valid_28 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'valid_28
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'valid_38
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.heap<code
d_heap'60'code_30 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'60'code_30
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'60'code_40
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.intervals-disjoint
d_intervals'45'disjoint_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_32 v0
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.du_intervals'45'disjoint_68
-- Once.CCC.Target.X86-32.RuntimeParams._.stack-bounds
d_stack'45'bounds_34 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_34
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'45'bounds_44
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.stack-upper
d_stack'45'upper_36 :: Integer
d_stack'45'upper_36
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'45'upper_26
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.stack<code
d_stack'60'code_38 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'60'code_38
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'60'code_64
      (coe d_x86'45'32'45'runtime_10)
-- Once.CCC.Target.X86-32.RuntimeParams._.stack<heap
d_stack'60'heap_40 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'60'heap_40
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'60'heap_36
      (coe d_x86'45'32'45'runtime_10)
