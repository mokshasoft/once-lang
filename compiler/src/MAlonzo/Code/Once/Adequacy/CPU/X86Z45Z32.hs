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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Arith.Backend.CallAnswer
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.TraceMonad

-- Once.Adequacy.CPU.X86-32.step-budget-x86-32
d_step'45'budget'45'x86'45'32_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.step-budget-x86-32"
-- Once.Adequacy.CPU.X86-32.ev-x86-32
d_ev'45'x86'45'32_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.ev-x86-32"
-- Once.Adequacy.CPU.X86-32.call-at-x86-32
d_call'45'at'45'x86'45'32_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.call-at-x86-32"
-- Once.Adequacy.CPU.X86-32.block-env
d_block'45'env_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
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
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                    (coe d_block'45'env_14 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CPU.X86-32.step-budget-x86-32-adequate
d_step'45'budget'45'x86'45'32'45'adequate_32
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.step-budget-x86-32-adequate"
-- Once.Adequacy.CPU.X86-32.run-trace-x86-32
d_run'45'trace'45'x86'45'32_34 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_296 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace'45'x86'45'32_34 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_234
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_316
              (coe v3)))
      (coe
         (\ v3 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_314
              (coe v3)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_692)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_418)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_matchCall_10)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace.d_ret'45'call_18
         (coe
            MAlonzo.Code.Once.Arith.Backend.CallAnswer.du_answer'45'at_220
            (coe v0) (coe d_call'45'at'45'x86'45'32_12)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimX86Z45Z32.du_val'45'x86'45'32_272
              v3 v4))
      (coe
         d_step'45'budget'45'x86'45'32_8
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_blocks_26 (coe v1))
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_code_22 (coe v1))
         v2)
      (coe d_ev'45'x86'45'32_10)
      (coe
         d_block'45'env_14
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_blocks_26 (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_code_22 (coe v1))
      (coe v2)
      (coe
         d_step'45'budget'45'x86'45'32'45'adequate_32 v0
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_blocks_26 (coe v1))
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_code_22 (coe v1))
         v2)
-- Once.Adequacy.CPU.X86-32.decode-x86-32
d_decode'45'x86'45'32_42
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.decode-x86-32"
-- Once.Adequacy.CPU.X86-32.assemble-x86-32
d_assemble'45'x86'45'32_44
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.assemble-x86-32"
-- Once.Adequacy.CPU.X86-32.as-faithful-x86-32
d_as'45'faithful'45'x86'45'32_48
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CPU.X86-32.as-faithful-x86-32"
-- Once.Adequacy.CPU.X86-32.arch-semantics
d_arch'45'semantics_50 ::
  MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10
d_arch'45'semantics_50
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.C_constructor_90
      (\ v0 ->
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_initStateAt_330
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46 (0 :: Integer)
              (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_entry_24 (coe v0))))
      (\ v0 ->
         coe
           MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_run_736
           (MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_code_22 (coe v0)))
      d_run'45'trace'45'x86'45'32_34 d_decode'45'x86'45'32_42
      d_assemble'45'x86'45'32_44
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_print_84 (\ v0 -> v0)
