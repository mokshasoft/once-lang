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
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR

-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState
d_FlatState_16 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.fetch
d_fetch_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_64 ~v0 ~v1 = du_fetch_64
du_fetch_64 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_64 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.flat-exec-instr
d_flat'45'exec'45'instr_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_flat'45'exec'45'instr_84 v0 ~v1 = du_flat'45'exec'45'instr_84 v0
du_flat'45'exec'45'instr_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
du_flat'45'exec'45'instr_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.falloc
d_falloc_148 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_148 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_76 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fclosure
d_fclosure_150 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_150 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.floc
d_floc_152 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_152 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_74 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fpc
d_fpc_154 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_154 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_78 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext._.FlatState.fret
d_fret_156 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> [Integer]
d_fret_156 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_80 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.EntryLike
d_EntryLike_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> ()
d_EntryLike_158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.Reachable
d_Reachable_178 a0 a1 a2 a3 a4 = ()
data T_Reachable_178
  = C_reach'45'start_186 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_reach'45'step_192 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 T_Reachable_178
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.Emitted
d_Emitted_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_Emitted_194 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt
d_RunAt_204 a0 a1 a2 a3 = ()
data T_RunAt_204
  = C_mkRunAt_226 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                  T_Reachable_178
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-ir
d_run'45'ir_218 :: T_RunAt_204 -> MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_218 v0
  = case coe v0 of
      C_mkRunAt_226 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-emit
d_run'45'emit_220 ::
  T_RunAt_204 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_220 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-heap
d_run'45'heap_222 :: T_RunAt_204 -> AgdaAny
d_run'45'heap_222 v0
  = case coe v0 of
      C_mkRunAt_226 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.RunAt.run-reach
d_run'45'reach_224 :: T_RunAt_204 -> T_Reachable_178
d_run'45'reach_224 v0
  = case coe v0 of
      C_mkRunAt_226 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RunContext.run-emitted
d_run'45'emitted_232 ::
  T_RunAt_204 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_232 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_run'45'ir_218 (coe v0)) erased
