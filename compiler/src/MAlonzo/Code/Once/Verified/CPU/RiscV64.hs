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

module MAlonzo.Code.Once.Verified.CPU.RiscV64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.CPU.RiscV64.run-trace-riscv64
d_run'45'trace'45'riscv64_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.RiscV64.run-trace-riscv64"
-- Once.Verified.CPU.RiscV64.decode-riscv64
d_decode'45'riscv64_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.RiscV64.decode-riscv64"
-- Once.Verified.CPU.RiscV64.assemble-riscv64
d_assemble'45'riscv64_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.RiscV64.assemble-riscv64"
-- Once.Verified.CPU.RiscV64.arch-semantics
d_arch'45'semantics_14 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_14
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.C_constructor_56
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_278
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_run_712
      d_run'45'trace'45'riscv64_8 d_decode'45'riscv64_10
      d_assemble'45'riscv64_12
