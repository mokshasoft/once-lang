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

module MAlonzo.Code.Once.CCC.Codegen.IRObsCorrectFlat where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.FlatEvents

-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState
d_FlatState_16 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.forced
d_forced_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_forced_70 ~v0 ~v1 = du_forced_70
du_forced_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_forced_70 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_666
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.falloc
d_falloc_88 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_falloc_88 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_66 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.floc
d_floc_90 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_floc_90 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.fpc
d_fpc_92 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 -> Integer
d_fpc_92 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.BeforeFrontier
d_BeforeFrontier_96 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ValidAtWF
d_ValidAtWF_108 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.flat-events
d_flat'45'events_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_140 v0 ~v1 = du_flat'45'events_140 v0
du_flat'45'events_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_140 v0
  = coe
      MAlonzo.Code.Once.Verified.FlatEvents.d_flat'45'events_222 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.μ-layer-iso
d_μ'45'layer'45'iso_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522
d_μ'45'layer'45'iso_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_μ'45'layer'45'iso_164 v9
du_μ'45'layer'45'iso_164 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522
du_μ'45'layer'45'iso_164 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_888 v6 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.flat-run
d_flat'45'run_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_flat'45'run_182 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_flat'45'run_182 v0 v2 v3 v4 v5 v6 v7
du_flat'45'run_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
du_flat'45'run_182 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_exec'45'flat_200 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_690
         (coe v2) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlat_70 (coe v5) (coe v6)
         (coe (0 :: Integer)))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.flat-run-keeps-next-slot
d_flat'45'run'45'keeps'45'next'45'slot_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_204 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.alg-run-keeps-frontier-0
d_alg'45'run'45'keeps'45'frontier'45'0_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alg'45'run'45'keeps'45'frontier'45'0_226 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_250 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_MachineRefinesObsF_250
  = C_constructor_292 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_282 ::
  T_MachineRefinesObsF_250 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_282 v0
  = case coe v0 of
      C_constructor_292 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_290 ::
  T_MachineRefinesObsF_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_290 v0
  = case coe v0 of
      C_constructor_292 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 -> ()
d_IRObsCorrectF_298 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct
d_cata'45'correct_324
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest
d_obs'45'correct'45'rest_332
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_18 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_522 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_MachineRefinesObsF_250
d_ir'45'obs'45'correct_340 v0 v1 v2 v3 v4
  = let v5 = coe d_obs'45'correct'45'rest_332 v0 v1 v2 v3 v4 in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.CCC.IR.C_Cata_120 v7 v9
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                  -> coe
                       d_cata'45'correct_324 v0 v1 v10 v7 v3 v9
                       (d_ir'45'obs'45'correct_340
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v10) (coe v3))
                          (coe v3) (coe v9))
                _ -> coe v5
         _ -> coe v5)
