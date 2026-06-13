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

module MAlonzo.Code.Once.Verified.CPU.X86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.CPU.X86-32.run-trace-x86-32
d_run'45'trace'45'x86'45'32_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-32.run-trace-x86-32"
-- Once.Verified.CPU.X86-32.decode-x86-32
d_decode'45'x86'45'32_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-32.decode-x86-32"
-- Once.Verified.CPU.X86-32.assemble-x86-32
d_assemble'45'x86'45'32_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.X86-32.assemble-x86-32"
-- Once.Verified.CPU.X86-32.arch-semantics
d_arch'45'semantics_14 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18
d_arch'45'semantics_14
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.C_constructor_64
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initState_166
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_run_504
      d_run'45'trace'45'x86'45'32_8 d_decode'45'x86'45'32_10
      d_assemble'45'x86'45'32_12
