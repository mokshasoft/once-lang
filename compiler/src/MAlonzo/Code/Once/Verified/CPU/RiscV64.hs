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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.CPU.RiscV64.observe-riscv64
d_observe'45'riscv64_8 ::
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Maybe Integer
d_observe'45'riscv64_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> let v2
                 = MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_268
                     (coe v1) in
           coe
             (if coe v2
                then coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_104
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262 (coe v1))
                          (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_a0_20))
                else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.CPU.RiscV64.decode-riscv64
d_decode'45'riscv64_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.CPU.RiscV64.decode-riscv64"
-- Once.Verified.CPU.RiscV64.arch-semantics
d_arch'45'semantics_22 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18
d_arch'45'semantics_22
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.C_constructor_58
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_278
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_run_712
      d_observe'45'riscv64_8 d_decode'45'riscv64_20
