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

module MAlonzo.Code.Once.Adequacy.FlatEvents where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState
d_FlatState_14 a0 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.fetch
d_fetch_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_80 ~v0 = du_fetch_80
du_fetch_80 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_80 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.falloc
d_falloc_190 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_190 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_82 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.fclosure
d_fclosure_192 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_192 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_88 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.floc
d_floc_194 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_194 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.fpc
d_fpc_196 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_196 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.fret
d_fret_198 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_198 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_86 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatSteps
d_FlatSteps_204 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatSteps-++
d_FlatSteps'45''43''43'_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228
d_FlatSteps'45''43''43'_206 ~v0 = du_FlatSteps'45''43''43'_206
du_FlatSteps'45''43''43'_206 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228
du_FlatSteps'45''43''43'_206 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_860
      v6 v7
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified
d_RunReified_208 a0 a1 a2 a3 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.chain
d_chain_260 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228
d_chain_260 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_chain_746 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.fuel-split
d_fuel'45'split_262 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_262 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.rest-fuel
d_rest'45'fuel_264 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  Integer
d_rest'45'fuel_264 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_rest'45'fuel_742
      (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.settle
d_settle_266 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_settle_266 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settle_744 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.settled
d_settled_268 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_268 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settled_748 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.steps-len
d_steps'45'len_270 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  Integer
d_steps'45'len_270 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_steps'45'len_740
      (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace.decode-ℕ
d_decode'45'ℕ_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_decode'45'ℕ_272 ~v0 v1 = du_decode'45'ℕ_272 v1
du_decode'45'ℕ_272 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_decode'45'ℕ_272 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Int_136
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                _ -> coe v1
         _ -> coe v1)
-- Once.Adequacy.FlatEvents.FlatEventTrace.machine-event
d_machine'45'event_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122
d_machine'45'event_280 ~v0 v1 ~v2 v3 v4
  = du_machine'45'event_280 v1 v3 v4
du_machine'45'event_280 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122
du_machine'45'event_280 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Denotation.Trace.d_isInt'63'_120 (coe v0) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_132
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v1))
                (coe du_decode'45'ℕ_272 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_132
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v1)) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FlatEvents.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_ev'45'of'45'loc_304 ~v0 v1 v2 = du_ev'45'of'45'loc_304 v1 v2
du_ev'45'of'45'loc_304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_ev'45'of'45'loc_304 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v3 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Once.SigOp.Info.du_go_224
                        (coe MAlonzo.Code.Once.SigOp.Info.d_sem_176 (coe v5)) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Once.SigOp.Info.C_Pure_124
                     -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   MAlonzo.Code.Once.SigOp.Info.C_Emits_126
                     -> coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             du_machine'45'event_280 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   MAlonzo.Code.Once.SigOp.Info.C_Halts_128
                     -> coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             du_machine'45'event_280 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
-- Once.Adequacy.FlatEvents.FlatEventTrace.event-of
d_event'45'of_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_326 ~v0 v1 v2 = du_event'45'of_326 v1 v2
du_event'45'of_326 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_326 v0 v1
  = coe
      du_ev'45'of'45'loc_304 (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v1))
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events
d_flat'45'events_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_332 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_flat'45'events'45'step_334 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_80 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'step_334 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      else coe
             d_flat'45'events'45'fetch_336 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_210 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_84 (coe v4)))
             (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'fetch_336 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_326 (coe v5) (coe v4))
             (coe
                d_flat'45'events_332 (coe v0) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076 v0
                   v5 v3 v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-halted
d_flat'45'events'45'halted_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'halted_370 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_400 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events
d_chain'45'events_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_chain'45'events_472 v0 v1 ~v2 v3 ~v4 v5
  = du_chain'45'events_472 v0 v1 v3 v5
du_chain'45'events_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_chain'45'events_472 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_234
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__244 v7 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_326 (coe v7) (coe v2))
             (coe
                du_chain'45'events_472 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1076 v0
                   v7 v1 v2)
                (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_484 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_494 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_512 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_528 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_570 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_598 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_228 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_618 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_628 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_720 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_686 = erased
