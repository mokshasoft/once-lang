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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Size
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRObsCorrectFlat.fits-erase
d_fits'45'erase_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
d_fits'45'erase_10 ~v0 v1 = du_fits'45'erase_10 v1
du_fits'45'erase_10 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
du_fits'45'erase_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_198
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'int_512
      MAlonzo.Code.Once.Type.C_fits'45'float_200
        -> coe MAlonzo.Code.Once.IRTy.C_fits'45'float_514
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState
d_FlatState_20 a0 a1 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.fetch
d_fetch_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048
d_fetch_50 ~v0 ~v1 = du_fetch_50
du_fetch_50 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048
du_fetch_50 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_142
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.forced
d_forced_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_forced_74 ~v0 ~v1 = du_forced_74
du_forced_74 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_forced_74 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_forced_666
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.falloc
d_falloc_92 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_falloc_92 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_66 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.floc
d_floc_94 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_floc_94 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.FlatState.fpc
d_fpc_96 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 -> Integer
d_fpc_96 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.exec-sigop-halts
d_exec'45'sigop'45'halts_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 -> Bool
d_exec'45'sigop'45'halts_100 ~v0 ~v1
  = du_exec'45'sigop'45'halts_100
du_exec'45'sigop'45'halts_100 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 -> Bool
du_exec'45'sigop'45'halts_100 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'sigop'45'halts_2528
      v2
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_exec'45'sigop'45'output'45'of_104 v0 ~v1
  = du_exec'45'sigop'45'output'45'of_104 v0
du_exec'45'sigop'45'output'45'of_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_exec'45'sigop'45'output'45'of_104 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'sigop'45'output'45'of_2502
      (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.BeforeFrontier
d_BeforeFrontier_114 a0 a1 a2 a3 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ResultPlace
d_ResultPlace_126 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ValidAtWF
d_ValidAtWF_128 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.prim-sv
d_prim'45'sv_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_134 ~v0 ~v1 = du_prim'45'sv_134
du_prim'45'sv_134 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_134 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_prim'45'sv_506
      v1 v2
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.event-of
d_event'45'of_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_176 ~v0 ~v1 = du_event'45'of_176
du_event'45'of_176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_176
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_216
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.flat-events
d_flat'45'events_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_178 v0 ~v1 = du_flat'45'events_178 v0
du_flat'45'events_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_178 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_222 (coe v0)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.Readable
d_Readable_184 a0 a1 a2 = ()
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.μ-layer-iso
d_μ'45'layer'45'iso_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514
d_μ'45'layer'45'iso_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_μ'45'layer'45'iso_226 v9
du_μ'45'layer'45'iso_226 ::
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514
du_μ'45'layer'45'iso_226 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_862 v6 v8
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.flat-run
d_flat'45'run_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_flat'45'run_244 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_flat'45'run_244 v0 v2 v3 v4 v5 v6 v7
du_flat'45'run_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
du_flat'45'run_244 v0 v1 v2 v3 v4 v5 v6
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
d_flat'45'run'45'keeps'45'next'45'slot_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'run'45'keeps'45'next'45'slot_266 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.alg-run-keeps-frontier-0
d_alg'45'run'45'keeps'45'frontier'45'0_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alg'45'run'45'keeps'45'frontier'45'0_288 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF
d_MachineRefinesObsF_312 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_MachineRefinesObsF_312
  = C_constructor_354 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.traces-agree
d_traces'45'agree_344 ::
  T_MachineRefinesObsF_312 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_traces'45'agree_344 v0
  = case coe v0 of
      C_constructor_354 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.MachineRefinesObsF.value-realized
d_value'45'realized_352 ::
  T_MachineRefinesObsF_312 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_value'45'realized_352 v0
  = case coe v0 of
      C_constructor_354 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.InputAt
d_InputAt_364 a0 a1 a2 a3 a4 a5 = ()
data T_InputAt_364
  = C_in'45'loc_374 |
    C_in'45'reg_378 MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.IRObsCorrectF
d_IRObsCorrectF_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IRObsCorrectF_384 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct
d_cata'45'correct_410
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.cata-correct"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest
d_obs'45'correct'45'rest_418
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-rest"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.sigop-halts-false
d_sigop'45'halts'45'false_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'halts'45'false_428 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.sv-loc-of
d_sv'45'loc'45'of_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'loc'45'of_442 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-sigop-value-reg
d_pure'45'sigop'45'value'45'reg_468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'value'45'reg_468 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_488 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_526 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-sigop-value-correct
d_pure'45'sigop'45'value'45'correct_598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pure'45'sigop'45'value'45'correct_598 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_668 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.step2
d_step2_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step2_712 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.pure-obs-correct-sigop
d_pure'45'obs'45'correct'45'sigop_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> T_MachineRefinesObsF_312
d_pure'45'obs'45'correct'45'sigop_742 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
                                      ~v8 ~v9 ~v10 v11 v12 v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pure'45'obs'45'correct'45'sigop_742
      v0 v2 v3 v4 v5 v11 v12 v13 v16
du_pure'45'obs'45'correct'45'sigop_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  T_MachineRefinesObsF_312
du_pure'45'obs'45'correct'45'sigop_742 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      C_constructor_354
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
              erased))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Once.IR.C_Stack_6)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe
                  MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_66
                  (coe
                     du_flat'45'run_244 (coe v0) (coe (2 :: Integer))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                     (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v1) (coe v2) (coe v3))
                     (coe v6) (coe v7)))
               (coe
                  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_at'45'reg_978 v5
                  (coe du_fits'45'erase_10 (coe v4)) v8 v8))))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.ev-[]
d_ev'45''91''93'_784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ev'45''91''93'_784 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.mach-[]
d_mach'45''91''93'_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mach'45''91''93'_800 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.denot-[]
d_denot'45''91''93'_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_denot'45''91''93'_806 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.keeps-alloc
d_keeps'45'alloc_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'alloc_814 = erased
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness._.before
d_before_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.T_Readable_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
d_before_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_before_824 v16
du_before_824 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610
du_before_824 v0 = coe v0
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.obs-correct-sigop
d_obs'45'correct'45'sigop_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> T_MachineRefinesObsF_312
d_obs'45'correct'45'sigop_838 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v3) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate.du_readable'63'_178
                 (coe v2) in
       coe
         (case coe v5 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
              -> case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                     -> let v9
                              = coe
                                  MAlonzo.Code.Once.SigOp.Info.du_go_224
                                  (coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v4)) in
                        coe
                          (case coe v9 of
                             MAlonzo.Code.Once.SigOp.Info.C_Pure_124
                               -> coe
                                    (\ v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ->
                                       coe
                                         du_pure'45'obs'45'correct'45'sigop_742 (coe v0) (coe v2)
                                         (coe v3) (coe v4) (coe v7) v13 v14 v15 v18)
                             MAlonzo.Code.Once.SigOp.Info.C_Emits_126
                               -> coe
                                    d_obs'45'correct'45'rest_418 v0 v1
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_SigOp_154 (coe v2) (coe v3) (coe v4))
                             MAlonzo.Code.Once.SigOp.Info.C_Halts_128
                               -> coe
                                    d_obs'45'correct'45'rest_418 v0 v1
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_SigOp_154 (coe v2) (coe v3) (coe v4))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          d_obs'45'correct'45'rest_418 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v2) (coe v3) (coe v4))
                   _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
              -> coe
                   d_obs'45'correct'45'rest_418 v0 v1
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                   (coe MAlonzo.Code.Once.IR.C_SigOp_154 (coe v2) (coe v3) (coe v4))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-size-f
d_comp'45'size'45'f_920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_comp'45'size'45'f_920 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_comp'45'size'45'f_920 v2 v3 v4 v5 v6 v7
du_comp'45'size'45'f_920 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_comp'45'size'45'f_920 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
            (coe
               MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
               (coe v4)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
                  (coe v3)))))
      (coe v5)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-size-g
d_comp'45'size'45'g_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_comp'45'size'45'g_938 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_comp'45'size'45'g_938 v2 v3 v4 v5 v6 v7
du_comp'45'size'45'g_938 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_comp'45'size'45'g_938 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
               (coe v3)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v0) (coe v1)
                  (coe v4))
               (coe
                  MAlonzo.Code.Once.IR.Size.d_ir'45'size_10 (coe v1) (coe v2)
                  (coe v3)))))
      (coe v5)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-step
d_comp'45'step_962
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-step"
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.comp-obs-correct
d_comp'45'obs'45'correct_974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_InputAt_364 -> T_MachineRefinesObsF_312) ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.IR.T_AllocMode_4 ->
   AgdaAny ->
   MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_InputAt_364 -> T_MachineRefinesObsF_312) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> T_MachineRefinesObsF_312
d_comp'45'obs'45'correct_974 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      d_comp'45'step_962 v0 v1 v2 v3 v4 v5 v6 v11 v13 v14
      (coe
         du_comp'45'size'45'g_938 (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v9))
      v7
      (coe
         v8
         (coe
            du_comp'45'size'45'f_920 (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v9))
         v10 v11 v12 v13 v14 v15 v16 v17 v18 v19)
-- Once.CCC.Codegen.IRObsCorrectFlat.IRObsCorrectFlatness.ir-obs-correct
d_ir'45'obs'45'correct_1012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_514 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputAt_364 -> T_MachineRefinesObsF_312
d_ir'45'obs'45'correct_1012 v0 v1 v2 v3 v4
  = let v5 = coe d_obs'45'correct'45'rest_418 v0 v1 v2 v3 v4 in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
           -> coe
                d_comp'45'obs'45'correct_974 (coe v0) (coe v1) (coe v2) (coe v7)
                (coe v3) (coe v9) (coe v10)
                (coe
                   d_ir'45'obs'45'correct_1012 (coe v0) (coe v1) (coe v7) (coe v3)
                   (coe v9))
                (coe
                   d_ir'45'obs'45'correct_1012 (coe v0) (coe v1) (coe v2) (coe v7)
                   (coe v10))
         MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                  -> coe
                       d_cata'45'correct_410 v0 v1 v10 v7 v3 v9
                       (d_ir'45'obs'45'correct_1012
                          (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v3))
                          (coe v3) (coe v9))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
           -> coe
                d_obs'45'correct'45'sigop_838 (coe v0) (coe v1) (coe v6) (coe v7)
                (coe v8)
         _ -> coe v5)
