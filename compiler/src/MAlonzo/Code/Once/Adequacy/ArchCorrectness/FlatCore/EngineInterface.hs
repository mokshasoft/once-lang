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
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter
d_Emitter_14 a0 a1 = ()
data T_Emitter_14
  = C_constructor_192 (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
                       [AgdaAny])
                      ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
                       [AgdaAny])
                      ([AgdaAny] -> Integer -> Maybe AgdaAny) (AgdaAny -> Bool)
                      (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny)
                      (MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
                       [AgdaAny] -> Integer -> Maybe Integer)
                      (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50)
                      ([AgdaAny] ->
                       MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.Instr
d_Instr_104 :: T_Emitter_14 -> ()
d_Instr_104 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.compile-abstract
d_compile'45'abstract_106 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [AgdaAny]
d_compile'45'abstract_106 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.compile-trace
d_compile'45'trace_108 ::
  T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [AgdaAny]
d_compile'45'trace_108 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.ct-nil
d_ct'45'nil_110 ::
  T_Emitter_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ct'45'nil_110 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.ct-cons
d_ct'45'cons_116 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ct'45'cons_116 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch
d_mfetch_118 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_118 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-nil
d_mfetch'45'nil_122 ::
  T_Emitter_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'nil_122 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-zero
d_mfetch'45'zero_128 ::
  T_Emitter_14 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'zero_128 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mfetch-suc
d_mfetch'45'suc_136 ::
  T_Emitter_14 ->
  AgdaAny ->
  [AgdaAny] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mfetch'45'suc_136 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.is-label?
d_is'45'label'63'_138 :: T_Emitter_14 -> AgdaAny -> Bool
d_is'45'label'63'_138 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.mk-label
d_mk'45'label_140 ::
  T_Emitter_14 -> MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny
d_mk'45'label_140 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-go
d_find'45'label'45'go_142 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] -> Integer -> Maybe Integer
d_find'45'label'45'go_142 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-nil
d_find'45'label'45'nil_148 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'nil_148 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.skip-law
d_skip'45'law_158 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  AgdaAny ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'law_158 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.label-hit
d_label'45'hit_168 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'hit_168 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.label-miss
d_label'45'miss_178 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'miss_178 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.headView
d_headView_182 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView.T_HeadView_50
d_headView_182 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label
d_find'45'label_184 ::
  T_Emitter_14 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 -> Maybe Integer
d_find'45'label_184 v0
  = case coe v0 of
      C_constructor_192 v2 v3 v6 v10 v11 v12 v17 v18 -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Emitter.find-label-def
d_find'45'label'45'def_190 ::
  T_Emitter_14 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'def_190 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine
d_Machine_196 a0 a1 a2 = ()
data T_Machine_196
  = C_constructor_356 (AgdaAny -> AgdaAny -> Integer)
                      (AgdaAny -> Integer -> Maybe Integer) (AgdaAny -> Bool)
                      (AgdaAny -> Integer)
                      ([AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny)
                      (Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.Instr
d_Instr_202 :: T_Emitter_14 -> ()
d_Instr_202 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.mfetch
d_mfetch_204 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_204 v0 = coe d_mfetch_118 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine._.Instr
d_Instr_280 :: T_Emitter_14 -> T_Machine_196 -> ()
d_Instr_280 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine._.mfetch
d_mfetch_282 ::
  T_Emitter_14 ->
  T_Machine_196 -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_282 v0 ~v1 = du_mfetch_282 v0
du_mfetch_282 ::
  T_Emitter_14 -> [AgdaAny] -> Integer -> Maybe AgdaAny
du_mfetch_282 v0 = coe d_mfetch_118 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.State
d_State_284 :: T_Machine_196 -> ()
d_State_284 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.rreg
d_rreg_286 :: T_Machine_196 -> AgdaAny -> AgdaAny -> Integer
d_rreg_286 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.memory
d_memory_288 ::
  T_Machine_196 -> AgdaAny -> Integer -> Maybe Integer
d_memory_288 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.xhalted
d_xhalted_290 :: T_Machine_196 -> AgdaAny -> Bool
d_xhalted_290 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.xpc
d_xpc_292 :: T_Machine_196 -> AgdaAny -> Integer
d_xpc_292 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.mexecInstr
d_mexecInstr_294 ::
  T_Machine_196 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_294 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec
d_exec_296 ::
  T_Machine_196 -> Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny
d_exec_296 v0
  = case coe v0 of
      C_constructor_356 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-zero
d_exec'45'zero_302 ::
  T_Machine_196 ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'zero_302 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-halted
d_exec'45'halted_310 ::
  T_Machine_196 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'halted_310 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-end
d_exec'45'end_320 ::
  T_Machine_196 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'end_320 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-stuck
d_exec'45'stuck_330 ::
  T_Machine_196 ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'stuck_330 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-step-halt
d_exec'45'step'45'halt_342 ::
  T_Machine_196 ->
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
d_exec'45'step'45'halt_342 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.Machine.exec-step-run
d_exec'45'step'45'run_354 ::
  T_Machine_196 ->
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
d_exec'45'step'45'run_354 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop
d_TraceLoop_362 a0 a1 a2 a3 = ()
data T_TraceLoop_362
  = C_constructor_468 (AgdaAny ->
                       Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
                      (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
                      ([AgdaAny] ->
                       MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.Instr
d_Instr_370 :: T_Emitter_14 -> T_Machine_196 -> ()
d_Instr_370 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.compile-abstract
d_compile'45'abstract_372 ::
  T_Emitter_14 ->
  T_Machine_196 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [AgdaAny]
d_compile'45'abstract_372 v0 ~v1 = du_compile'45'abstract_372 v0
du_compile'45'abstract_372 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [AgdaAny]
du_compile'45'abstract_372 v0
  = coe d_compile'45'abstract_106 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.State
d_State_376 :: T_Machine_196 -> ()
d_State_376 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.mexecInstr
d_mexecInstr_378 ::
  T_Machine_196 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_378 v0 = coe d_mexecInstr_294 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface._.xhalted
d_xhalted_380 :: T_Machine_196 -> AgdaAny -> Bool
d_xhalted_380 v0 = coe d_xhalted_290 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.Instr
d_Instr_420 ::
  T_Emitter_14 -> T_Machine_196 -> T_TraceLoop_362 -> ()
d_Instr_420 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.compile-abstract
d_compile'45'abstract_422 ::
  T_Emitter_14 ->
  T_Machine_196 ->
  T_TraceLoop_362 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [AgdaAny]
d_compile'45'abstract_422 v0 ~v1 ~v2
  = du_compile'45'abstract_422 v0
du_compile'45'abstract_422 ::
  T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [AgdaAny]
du_compile'45'abstract_422 v0
  = coe d_compile'45'abstract_106 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.State
d_State_426 :: T_Machine_196 -> T_TraceLoop_362 -> ()
d_State_426 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.mexecInstr
d_mexecInstr_428 ::
  T_Machine_196 ->
  T_TraceLoop_362 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_428 v0 ~v1 = du_mexecInstr_428 v0
du_mexecInstr_428 ::
  T_Machine_196 -> [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
du_mexecInstr_428 v0 = coe d_mexecInstr_294 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop._.xhalted
d_xhalted_430 ::
  T_Machine_196 -> T_TraceLoop_362 -> AgdaAny -> Bool
d_xhalted_430 v0 ~v1 = du_xhalted_430 v0
du_xhalted_430 :: T_Machine_196 -> AgdaAny -> Bool
du_xhalted_430 v0 = coe d_xhalted_290 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.Payload
d_Payload_432 :: T_TraceLoop_362 -> ()
d_Payload_432 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.matchCall
d_matchCall_434 ::
  T_TraceLoop_362 ->
  AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_matchCall_434 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.ret-past
d_ret'45'past_436 :: T_TraceLoop_362 -> AgdaAny -> AgdaAny
d_ret'45'past_436 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.dispatchArith
d_dispatchArith_438 ::
  T_TraceLoop_362 -> AgdaAny -> AgdaAny -> AgdaAny
d_dispatchArith_438 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.ev-arch
d_ev'45'arch_440 ::
  T_TraceLoop_362 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_ev'45'arch_440 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.arith-env
d_arith'45'env_442 ::
  T_TraceLoop_362 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny
d_arith'45'env_442 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-call
d_sigop'45'call_444 ::
  T_TraceLoop_362 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_sigop'45'call_444 v0
  = case coe v0 of
      C_constructor_468 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-lowering
d_sigop'45'lowering_452 ::
  T_TraceLoop_362 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'lowering_452 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.sigop-matchCall
d_sigop'45'matchCall_456 ::
  T_TraceLoop_362 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'matchCall_456 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.TraceLoop.nonhalt-noncall
d_nonhalt'45'noncall_466 ::
  T_TraceLoop_362 ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nonhalt'45'noncall_466 = erased
