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
d_FlatState_12 a0 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.fetch
d_fetch_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_44 ~v0 = du_fetch_44
du_fetch_44 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_44 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_148
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.falloc
d_falloc_98 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_98 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_72 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.floc
d_floc_100 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_100 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatState.fpc
d_fpc_102 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 -> Integer
d_fpc_102 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatSteps
d_FlatSteps_108 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.FlatSteps-++
d_FlatSteps'45''43''43'_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132
d_FlatSteps'45''43''43'_110 ~v0 = du_FlatSteps'45''43''43'_110
du_FlatSteps'45''43''43'_110 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132
du_FlatSteps'45''43''43'_110 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.du_FlatSteps'45''43''43'_764
      v6 v7
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified
d_RunReified_112 a0 a1 a2 a3 = ()
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.chain
d_chain_164 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132
d_chain_164 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_chain_650 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.fuel-split
d_fuel'45'split_166 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fuel'45'split_166 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.rest-fuel
d_rest'45'fuel_168 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  Integer
d_rest'45'fuel_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_rest'45'fuel_646
      (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.settle
d_settle_170 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62
d_settle_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settle_648 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.settled
d_settled_172 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_settled_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_settled_652 (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace._.RunReified.steps-len
d_steps'45'len_174 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  Integer
d_steps'45'len_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.d_steps'45'len_644
      (coe v0)
-- Once.Adequacy.FlatEvents.FlatEventTrace.decode-ℕ
d_decode'45'ℕ_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_decode'45'ℕ_176 ~v0 v1 = du_decode'45'ℕ_176 v1
du_decode'45'ℕ_176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_decode'45'ℕ_176 v0
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
d_machine'45'event_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122
d_machine'45'event_184 ~v0 v1 ~v2 v3 v4
  = du_machine'45'event_184 v1 v3 v4
du_machine'45'event_184 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122
du_machine'45'event_184 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Denotation.Trace.d_isInt'63'_120 (coe v0) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_132
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v1))
                (coe du_decode'45'ℕ_176 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_132
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_174 (coe v1)) (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FlatEvents.FlatEventTrace.ev-of-loc
d_ev'45'of'45'loc_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_ev'45'of'45'loc_208 ~v0 v1 v2 = du_ev'45'of'45'loc_208 v1 v2
du_ev'45'of'45'loc_208 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_ev'45'of'45'loc_208 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2288 v3 v4 v5
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
                             du_machine'45'event_184 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   MAlonzo.Code.Once.SigOp.Info.C_Halts_128
                     -> coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             du_machine'45'event_184 (coe v3) (coe v5)
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v1))
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
-- Once.Adequacy.FlatEvents.FlatEventTrace.event-of
d_event'45'of_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_230 ~v0 v1 v2 = du_event'45'of_230 v1 v2
du_event'45'of_230 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_230 v0 v1
  = coe
      du_ev'45'of'45'loc_208 (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v1))
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events
d_flat'45'events_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_236 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_flat'45'events'45'step_238 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_70 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-step
d_flat'45'events'45'step_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'step_238 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      else coe
             d_flat'45'events'45'fetch_240 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_148 (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_74 (coe v4)))
             (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-fetch
d_flat'45'events'45'fetch_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'fetch_240 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_230 (coe v5) (coe v4))
             (coe
                d_flat'45'events_236 (coe v0) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_262 v0
                   v5 v3 v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-halted
d_flat'45'events'45'halted_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'halted_274 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-[]
d_flat'45'events'45''91''93'_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45''91''93'_304 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events
d_chain'45'events_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_chain'45'events_376 v0 v1 ~v2 v3 ~v4 v5
  = du_chain'45'events_376 v0 v1 v3 v5
du_chain'45'events_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_chain'45'events_376 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C_'91''93'_138
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.C__'8759'__148 v7 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_event'45'of_230 (coe v7) (coe v2))
             (coe
                du_chain'45'events_376 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_262 v0
                   v7 v1 v2)
                (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-nil
d_chain'45'events'45'nil_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'nil_388 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-len0
d_chain'45'events'45'len0_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'len0_398 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst-len
d_chain'45'events'45'subst'45'len_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'len_416 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-steps
d_flat'45'events'45'steps_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'steps_432 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-++
d_chain'45'events'45''43''43'_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45''43''43'_474 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst
d_chain'45'events'45'subst_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst_502 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.chain-events-subst-start
d_chain'45'events'45'subst'45'start_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_FlatSteps_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain'45'events'45'subst'45'start_522 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-settled
d_flat'45'events'45'settled_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'settled_532 = erased
-- Once.Adequacy.FlatEvents.FlatEventTrace.flat-events-reify
d_flat'45'events'45'reify_590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatStepLemmas.T_RunReified_624 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'events'45'reify_590 = erased
