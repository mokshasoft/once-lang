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

module MAlonzo.Code.Once.Adequacy.CPU.RiscV64 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Adequacy.CPU.RiscV64.step-budget-riscv64
d_step'45'budget'45'riscv64_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.step-budget-riscv64"
-- Once.Adequacy.CPU.RiscV64.ev-riscv64
d_ev'45'riscv64_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.ev-riscv64"
-- Once.Adequacy.CPU.RiscV64.arith-env-riscv64
d_arith'45'env'45'riscv64_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.arith-env-riscv64"
-- Once.Adequacy.CPU.RiscV64.run-trace-riscv64
d_run'45'trace'45'riscv64_14 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace'45'riscv64_14 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_268
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_266 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_fetch_330)
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.du_execInstr_338 v3
           v4)
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch.du_dispatch'45'arith_18
              (\ v5 v6 v7 ->
                 coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64.du_val'45'riscv64_196
                   v5 v6)
              v2 v4))
      (coe d_step'45'budget'45'riscv64_8) (coe d_ev'45'riscv64_10)
      (coe d_arith'45'env'45'riscv64_12 v0) (coe v0) (coe v1)
-- Once.Adequacy.CPU.RiscV64.decode-riscv64
d_decode'45'riscv64_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.decode-riscv64"
-- Once.Adequacy.CPU.RiscV64.assemble-riscv64
d_assemble'45'riscv64_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.assemble-riscv64"
-- Once.Adequacy.CPU.RiscV64.arch-semantics
d_arch'45'semantics_24 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_24
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_56
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initState_278
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_run_720
      d_run'45'trace'45'riscv64_14 d_decode'45'riscv64_20
      d_assemble'45'riscv64_22
