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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState
d_FlatState_22 a0 a1 a2 a3 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.fetch
d_fetch_110 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
d_fetch_110 ~v0 ~v1 ~v2 ~v3 = du_fetch_110
du_fetch_110 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
du_fetch_110 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.flat-exec-instr
d_flat'45'exec'45'instr_154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_154 ~v0 v1 ~v2 ~v3
  = du_flat'45'exec'45'instr_154 v1
du_flat'45'exec'45'instr_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_154 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.falloc
d_falloc_316 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_316 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.fclosure
d_fclosure_318 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_318 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.flink
d_flink_320 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_320 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.floc
d_floc_322 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408
d_floc_322 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.fpc
d_fpc_324 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_324 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext._.FlatState.fret
d_fret_326 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_326 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.EntryLike
d_EntryLike_340 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_340 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.Reachable
d_Reachable_360 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Reachable_360
  = C_reach'45'start_368 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_reach'45'step_374 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 T_Reachable_360
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.Emitted
d_Emitted_376 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] -> ()
d_Emitted_376 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.call-not-jmp
d_call'45'not'45'jmp_388 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'45'not'45'jmp_388 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.call-not-ret
d_call'45'not'45'ret_400 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'45'not'45'ret_400 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.LinkedImage
d_LinkedImage_408 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_LinkedImage_408 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt
d_RunAt_418 a0 a1 a2 a3 a4 a5 = ()
data T_RunAt_418
  = C_mkRunAt_444 [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
                  MAlonzo.Code.Once.IR.T_IR_16 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                  T_Reachable_360
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt.run-tbl
d_run'45'tbl_434 ::
  T_RunAt_418 -> [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_434 v0
  = case coe v0 of
      C_mkRunAt_444 v1 v2 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt.run-ir
d_run'45'ir_436 :: T_RunAt_418 -> MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_436 v0
  = case coe v0 of
      C_mkRunAt_444 v1 v2 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt.run-emit
d_run'45'emit_438 ::
  T_RunAt_418 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_438 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt.run-linked
d_run'45'linked_440 ::
  T_RunAt_418 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_440 v0
  = case coe v0 of
      C_mkRunAt_444 v1 v2 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.RunAt.run-reach
d_run'45'reach_442 :: T_RunAt_418 -> T_Reachable_360
d_run'45'reach_442 v0
  = case coe v0 of
      C_mkRunAt_444 v1 v2 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext.run-emitted
d_run'45'emitted_450 ::
  T_RunAt_418 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_450 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_run'45'tbl_434 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_run'45'ir_436 (coe v0)) erased)
