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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.SigOp.Info

-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter
d_Emitter_14 a0 a1 = ()
data T_Emitter_14
  = C_constructor_200 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
                       [AgdaAny])
                      ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
                       [AgdaAny])
                      ([AgdaAny] -> Integer -> Maybe AgdaAny) (AgdaAny -> Bool)
                      (MAlonzo.Code.Once.CCC.Label.T_Label_28 -> AgdaAny)
                      (MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
                       [AgdaAny] -> Integer -> Maybe Integer)
                      (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50)
                      ([AgdaAny] ->
                       MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe Integer)
                      (MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2226 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.Instr
d_Instr_108 :: T_Emitter_14 -> ()
d_Instr_108 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.compile-abstract
d_compile'45'abstract_110 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [AgdaAny]
d_compile'45'abstract_110 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.compile-trace
d_compile'45'trace_112 ::
  T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  [AgdaAny]
d_compile'45'trace_112 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.ct-nil
d_ct'45'nil_114 ::
  T_Emitter_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ct'45'nil_114 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.ct-cons
d_ct'45'cons_120 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ct'45'cons_120 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch
d_mfetch_122 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_122 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-nil
d_mfetch'45'nil_126 ::
  T_Emitter_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'nil_126 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-zero
d_mfetch'45'zero_132 ::
  T_Emitter_14 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'zero_132 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-suc
d_mfetch'45'suc_140 ::
  T_Emitter_14 ->
  AgdaAny ->
  [AgdaAny] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'suc_140 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.is-label?
d_is'45'label'63'_142 :: T_Emitter_14 -> AgdaAny -> Bool
d_is'45'label'63'_142 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mk-label
d_mk'45'label_144 ::
  T_Emitter_14 -> MAlonzo.Code.Once.CCC.Label.T_Label_28 -> AgdaAny
d_mk'45'label_144 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-go
d_find'45'label'45'go_146 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] -> Integer -> Maybe Integer
d_find'45'label'45'go_146 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-nil
d_find'45'label'45'nil_152 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'nil_152 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.skip-law
d_skip'45'law_162 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  AgdaAny ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_162 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.label-hit
d_label'45'hit_172 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_172 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.label-miss
d_label'45'miss_182 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_182 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.headView
d_headView_186 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_186 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label
d_find'45'label_188 ::
  T_Emitter_14 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 -> Maybe Integer
d_find'45'label_188 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-def
d_find'45'label'45'def_194 ::
  T_Emitter_14 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'def_194 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.ctrl-len
d_ctrl'45'len_198 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2226 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ctrl'45'len_198 v0
  = case coe v0 of
      C_constructor_200 v2 v3 v6 v10 v11 v12 v17 v18 v20 -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine
d_Machine_204 a0 a1 a2 = ()
data T_Machine_204
  = C_constructor_368 (AgdaAny -> AgdaAny -> Integer)
                      (AgdaAny -> Integer -> Maybe Integer) (AgdaAny -> Bool)
                      (AgdaAny -> Integer)
                      ([AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny)
                      (Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.Instr
d_Instr_210 :: T_Emitter_14 -> ()
d_Instr_210 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.mfetch
d_mfetch_212 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_212 v0 = coe d_mfetch_122 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine._.Instr
d_Instr_290 :: T_Emitter_14 -> T_Machine_204 -> ()
d_Instr_290 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine._.mfetch
d_mfetch_292 ::
  T_Emitter_14 ->
  T_Machine_204 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_292 v0 ~v1 = du_mfetch_292 v0
du_mfetch_292 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
du_mfetch_292 v0 = coe d_mfetch_122 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.State
d_State_294 :: T_Machine_204 -> ()
d_State_294 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.rreg
d_rreg_296 :: T_Machine_204 -> AgdaAny -> AgdaAny -> Integer
d_rreg_296 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.memory
d_memory_298 ::
  T_Machine_204 -> AgdaAny -> Integer -> Maybe Integer
d_memory_298 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.xhalted
d_xhalted_300 :: T_Machine_204 -> AgdaAny -> Bool
d_xhalted_300 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.xpc
d_xpc_302 :: T_Machine_204 -> AgdaAny -> Integer
d_xpc_302 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.link-claim
d_link'45'claim_304 ::
  T_Machine_204 -> AgdaAny -> Integer -> Integer -> ()
d_link'45'claim_304 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.mexecInstr
d_mexecInstr_306 ::
  T_Machine_204 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_306 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec
d_exec_308 ::
  T_Machine_204 -> Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny
d_exec_308 v0
  = case coe v0 of
      C_constructor_368 v2 v3 v4 v5 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-zero
d_exec'45'zero_314 ::
  T_Machine_204 ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'zero_314 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-halted
d_exec'45'halted_322 ::
  T_Machine_204 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'halted_322 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-end
d_exec'45'end_332 ::
  T_Machine_204 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'end_332 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-stuck
d_exec'45'stuck_342 ::
  T_Machine_204 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'stuck_342 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-step-halt
d_exec'45'step'45'halt_354 ::
  T_Machine_204 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'step'45'halt_354 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-step-run
d_exec'45'step'45'run_366 ::
  T_Machine_204 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'step'45'run_366 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop
d_TraceLoop_374 a0 a1 a2 a3 = ()
data T_TraceLoop_374
  = C_constructor_484 (AgdaAny ->
                       Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
                      ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
                       MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56])
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.Instr
d_Instr_382 :: T_Emitter_14 -> T_Machine_204 -> ()
d_Instr_382 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.compile-abstract
d_compile'45'abstract_384 ::
  T_Emitter_14 ->
  T_Machine_204 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [AgdaAny]
d_compile'45'abstract_384 v0 ~v1 = du_compile'45'abstract_384 v0
du_compile'45'abstract_384 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [AgdaAny]
du_compile'45'abstract_384 v0
  = coe d_compile'45'abstract_110 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.State
d_State_388 :: T_Machine_204 -> ()
d_State_388 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.mexecInstr
d_mexecInstr_390 ::
  T_Machine_204 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_390 v0 = coe d_mexecInstr_306 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.xhalted
d_xhalted_392 :: T_Machine_204 -> AgdaAny -> Bool
d_xhalted_392 v0 = coe d_xhalted_300 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.Instr
d_Instr_434 ::
  T_Emitter_14 -> T_Machine_204 -> T_TraceLoop_374 -> ()
d_Instr_434 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.compile-abstract
d_compile'45'abstract_436 ::
  T_Emitter_14 ->
  T_Machine_204 ->
  T_TraceLoop_374 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [AgdaAny]
d_compile'45'abstract_436 v0 ~v1 ~v2
  = du_compile'45'abstract_436 v0
du_compile'45'abstract_436 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252 ->
  [AgdaAny]
du_compile'45'abstract_436 v0
  = coe d_compile'45'abstract_110 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.State
d_State_440 :: T_Machine_204 -> T_TraceLoop_374 -> ()
d_State_440 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.mexecInstr
d_mexecInstr_442 ::
  T_Machine_204 ->
  T_TraceLoop_374 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_442 v0 ~v1 = du_mexecInstr_442 v0
du_mexecInstr_442 ::
  T_Machine_204 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
du_mexecInstr_442 v0 = coe d_mexecInstr_306 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.xhalted
d_xhalted_444 ::
  T_Machine_204 -> T_TraceLoop_374 -> AgdaAny -> Bool
d_xhalted_444 v0 ~v1 = du_xhalted_444 v0
du_xhalted_444 :: T_Machine_204 -> AgdaAny -> Bool
du_xhalted_444 v0 = coe d_xhalted_300 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.Payload
d_Payload_446 :: T_TraceLoop_374 -> ()
d_Payload_446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.matchCall
d_matchCall_448 ::
  T_TraceLoop_374 ->
  AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_matchCall_448 v0
  = case coe v0 of
      C_constructor_484 v2 v3 v4 v5 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.ret-call
d_ret'45'call_450 ::
  T_TraceLoop_374 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_ret'45'call_450 v0
  = case coe v0 of
      C_constructor_484 v2 v3 v4 v5 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.dispatchArith
d_dispatchArith_452 ::
  T_TraceLoop_374 -> AgdaAny -> AgdaAny -> AgdaAny
d_dispatchArith_452 v0
  = case coe v0 of
      C_constructor_484 v2 v3 v4 v5 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.ev-arch
d_ev'45'arch_454 ::
  T_TraceLoop_374 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_ev'45'arch_454 v0
  = case coe v0 of
      C_constructor_484 v2 v3 v4 v5 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.ArithTable
d_ArithTable_456 ::
  T_TraceLoop_374 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  ()
d_ArithTable_456 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-call
d_sigop'45'call_458 ::
  T_TraceLoop_374 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_sigop'45'call_458 v0
  = case coe v0 of
      C_constructor_484 v2 v3 v4 v5 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-lowering
d_sigop'45'lowering_466 ::
  T_TraceLoop_374 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'lowering_466 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-matchCall
d_sigop'45'matchCall_470 ::
  T_TraceLoop_374 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'matchCall_470 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.leave-lowering
d_leave'45'lowering_472 ::
  T_TraceLoop_374 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'lowering_472 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.nonhalt-noncall
d_nonhalt'45'noncall_482 ::
  T_TraceLoop_374 ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonhalt'45'noncall_482 = erased
