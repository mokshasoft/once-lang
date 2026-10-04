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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.TraceMonad

-- Once.Adequacy.CPU.RiscV64.step-budget-riscv64
d_step'45'budget'45'riscv64_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.step-budget-riscv64"
-- Once.Adequacy.CPU.RiscV64.ev-riscv64
d_ev'45'riscv64_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.ev-riscv64"
-- Once.Adequacy.CPU.RiscV64.call-at-riscv64
d_call'45'at'45'riscv64_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.call-at-riscv64"
-- Once.Adequacy.CPU.RiscV64.block-env
d_block'45'env_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_block'45'env_14 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
                       (coe v1))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                    (coe d_block'45'env_14 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.RiscV64.run-trace-riscv64
d_run'45'trace'45'riscv64_24 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_408 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace'45'riscv64_24 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_228
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_424
              (coe v3)))
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_422 (coe v3)))
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_fetch_492)
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_execInstr_550)
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.RunTrace.d_ret'45'call_18
         (coe
            MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_220
            (coe v0) (coe d_call'45'at'45'riscv64_12)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch.du_dispatch'45'arith_18
              (\ v6 v7 v8 ->
                 coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimRiscV64.du_val'45'riscv64_310
                   v6 v7)
              v3 v5))
      (coe d_step'45'budget'45'riscv64_8) (coe d_ev'45'riscv64_10)
      (coe
         d_block'45'env_14
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_blocks_26 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_code_22 (coe v1))
      (coe v2)
-- Once.Adequacy.CPU.RiscV64.decode-riscv64
d_decode'45'riscv64_32
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.decode-riscv64"
-- Once.Adequacy.CPU.RiscV64.assemble-riscv64
d_assemble'45'riscv64_34
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.assemble-riscv64"
-- Once.Adequacy.CPU.RiscV64.as-faithful-riscv64
d_as'45'faithful'45'riscv64_38
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.RiscV64.as-faithful-riscv64"
-- Once.Adequacy.CPU.RiscV64.arch-semantics
d_arch'45'semantics_40 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_40
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_90
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_initStateAt_436
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46 (0 :: Integer)
              (MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_entry_24 (coe v0))))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_run_896
           (MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_code_22 (coe v0)))
      d_run'45'trace'45'riscv64_24 d_decode'45'riscv64_32
      d_assemble'45'riscv64_34
      MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_print_78 (\ v0 -> v0)
