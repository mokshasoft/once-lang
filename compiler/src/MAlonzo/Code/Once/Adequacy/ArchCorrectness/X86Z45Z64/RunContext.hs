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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RunContext where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy

-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState
d_FlatState_18 a0 a1 a2 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.fetch
d_fetch_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_66 ~v0 ~v1 ~v2 = du_fetch_66
du_fetch_66 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_66 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.flat-exec-instr
d_flat'45'exec'45'instr_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_86 ~v0 v1 ~v2
  = du_flat'45'exec'45'instr_86 v1
du_flat'45'exec'45'instr_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.falloc
d_falloc_150 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_150 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fclosure
d_fclosure_152 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_152 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.floc
d_floc_154 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_154 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fpc
d_fpc_156 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_156 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fret
d_fret_158 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_158 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.ir-stack-budget
d_ir'45'stack'45'budget_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_162 v0 ~v1 ~v2
  = du_ir'45'stack'45'budget_162 v0
du_ir'45'stack'45'budget_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_162 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_702
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.ir-to-trace
d_ir'45'to'45'trace_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_ir'45'to'45'trace_164 v0 ~v1 ~v2 = du_ir'45'to'45'trace_164 v0
du_ir'45'to'45'trace_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
du_ir'45'to'45'trace_164 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_684
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.EntryLike
d_EntryLike_166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_166 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.Reachable
d_Reachable_186 a0 a1 a2 a3 a4 a5 = ()
data T_Reachable_186
  = C_reach'45'start_194 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_reach'45'step_200 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 T_Reachable_186
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.Emitted
d_Emitted_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_Emitted_202 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt
d_RunAt_212 a0 a1 a2 a3 a4 = ()
data T_RunAt_212
  = C_mkRunAt_234 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                  T_Reachable_186
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-ir
d_run'45'ir_226 :: T_RunAt_212 -> MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_226 v0
  = case coe v0 of
      C_mkRunAt_234 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-emit
d_run'45'emit_228 ::
  T_RunAt_212 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_228 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-heap
d_run'45'heap_230 :: T_RunAt_212 -> AgdaAny
d_run'45'heap_230 v0
  = case coe v0 of
      C_mkRunAt_234 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-reach
d_run'45'reach_232 :: T_RunAt_212 -> T_Reachable_186
d_run'45'reach_232 v0
  = case coe v0 of
      C_mkRunAt_234 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.run-emitted
d_run'45'emitted_240 ::
  T_RunAt_212 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_240 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_run'45'ir_226 (coe v0)) erased
