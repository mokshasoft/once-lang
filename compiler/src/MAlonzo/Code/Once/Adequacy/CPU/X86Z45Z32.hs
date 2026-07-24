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

module MAlonzo.Code.Once.Adequacy.CPU.X86Z45Z32 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Adequacy.CPU.X86-32.step-budget-x86-32
d_step'45'budget'45'x86'45'32_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.step-budget-x86-32"
-- Once.Adequacy.CPU.X86-32.ev-x86-32
d_ev'45'x86'45'32_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.ev-x86-32"
-- Once.Adequacy.CPU.X86-32.arith-env-x86-32
d_arith'45'env'45'x86'45'32_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.arith-env-x86-32"
-- Once.Adequacy.CPU.X86-32.run-trace-x86-32
d_run'45'trace'45'x86'45'32_14 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_134 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace'45'x86'45'32_14 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_154
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_152
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_410)
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.du_execInstr_224
           v3 v4)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32.du_val'45'x86'45'32_152
              v2 v3))
      (coe d_step'45'budget'45'x86'45'32_8) (coe d_ev'45'x86'45'32_10)
      (coe d_arith'45'env'45'x86'45'32_12 v0) (coe v0) (coe v1)
-- Once.Adequacy.CPU.X86-32.decode-x86-32
d_decode'45'x86'45'32_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.decode-x86-32"
-- Once.Adequacy.CPU.X86-32.assemble-x86-32
d_assemble'45'x86'45'32_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.assemble-x86-32"
-- Once.Adequacy.CPU.X86-32.arch-semantics
d_arch'45'semantics_24 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_24
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_56
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initState_166
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_run_512
      d_run'45'trace'45'x86'45'32_14 d_decode'45'x86'45'32_20
      d_assemble'45'x86'45'32_22
