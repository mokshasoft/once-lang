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

module MAlonzo.Code.Once.Verified.FlatEvents where

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
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.Trace

-- Once.Verified.FlatEvents.FlatEventTrace._.FlatState
d_FlatState_12 a0 = ()
-- Once.Verified.FlatEvents.FlatEventTrace._.fetch
d_fetch_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060
d_fetch_42 ~v0 = du_fetch_42
du_fetch_42 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060
du_fetch_42 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_142
-- Once.Verified.FlatEvents.FlatEventTrace._.FlatState.falloc
d_falloc_84 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_falloc_84 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_66 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.FlatState.floc
d_floc_86 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_floc_86 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.FlatState.fpc
d_fpc_88 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 -> Integer
d_fpc_88 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.FlatSteps
d_FlatSteps_94 a0 a1 a2 a3 a4 = ()
-- Once.Verified.FlatEvents.FlatEventTrace._.FlatSteps-++
d_FlatSteps'45''43''43'_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118
d_FlatSteps'45''43''43'_96 ~v0 = du_FlatSteps'45''43''43'_96
du_FlatSteps'45''43''43'_96 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118
du_FlatSteps'45''43''43'_96 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_750
      v6 v7
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified
d_RunReified_98 a0 a1 a2 a3 = ()
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.chain
d_chain_150 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118
d_chain_150 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_chain_636 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.fuel-split
d_fuel'45'split_152 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_152 = erased
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.rest-fuel
d_rest'45'fuel_154 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  Integer
d_rest'45'fuel_154 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_rest'45'fuel_632
      (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.settle
d_settle_156 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56
d_settle_156 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settle_634 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.settled
d_settled_158 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_158 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settled_638 (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace._.RunReified.steps-len
d_steps'45'len_160 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  Integer
d_steps'45'len_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_steps'45'len_630
      (coe v0)
-- Once.Verified.FlatEvents.FlatEventTrace.decode-ℕ
d_decode'45'ℕ_162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  Maybe Integer
d_decode'45'ℕ_162 ~v0 v1 = du_decode'45'ℕ_162 v1
du_decode'45'ℕ_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  Maybe Integer
du_decode'45'ℕ_162 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_88 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Int_136
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                _ -> coe v1
         _ -> coe v1)
-- Once.Verified.FlatEvents.FlatEventTrace.machine-event
d_machine'45'event_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140
d_machine'45'event_170 ~v0 v1 ~v2 v3 v4
  = du_machine'45'event_170 v1 v3 v4
du_machine'45'event_170 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140
du_machine'45'event_170 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Verified.Trace.d_isInt'63'_138 (coe v0) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Once.Verified.Trace.C_mk'45'event_150
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_166 (coe v1))
                (coe du_decode'45'ℕ_162 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Verified.Trace.C_mk'45'event_150
                (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_name_166 (coe v1)) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.FlatEvents.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_ev'45'of'45'loc_194 ~v0 v1 v2 = du_ev'45'of'45'loc_194 v1 v2
du_ev'45'of'45'loc_194 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
du_ev'45'of'45'loc_194 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2110 v3 v4 v5
           -> let v6
                    = MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_170 (coe v5) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_144
                     -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_146
                     -> coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             du_machine'45'event_170 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_164
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_480 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_58)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_148
                     -> coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             du_machine'45'event_170 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_164
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_480 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_58)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
-- Once.Verified.FlatEvents.FlatEventTrace.event-of
d_event'45'of_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_event'45'of_216 ~v0 v1 v2 = du_event'45'of_216 v1 v2
du_event'45'of_216 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
du_event'45'of_216 v0 v1
  = coe
      du_ev'45'of'45'loc_194 (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v1))
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events
d_flat'45'events_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_flat'45'events_222 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_flat'45'events'45'step_224 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_486
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_64 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_flat'45'events'45'step_224 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      else coe
             d_flat'45'events'45'fetch_226 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_142 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_68 (coe v4)))
             (coe v2) (coe v3) (coe v4)
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_flat'45'events'45'fetch_226 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_216 (coe v5) (coe v4))
             (coe
                d_flat'45'events_222 (coe v0) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_174 v0
                   v5 v3 v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_266 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events
d_chain'45'events_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_chain'45'events_338 v0 v1 ~v2 v3 ~v4 v5
  = du_chain'45'events_338 v0 v1 v3 v5
du_chain'45'events_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
du_chain'45'events_338 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_124
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__134 v7 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_216 (coe v7) (coe v2))
             (coe
                du_chain'45'events_338 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_174 v0
                   v7 v1 v2)
                (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_350 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_360 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_378 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_394 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_436 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_464 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_484 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_494 = erased
-- Once.Verified.FlatEvents.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2060] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_552 = erased
