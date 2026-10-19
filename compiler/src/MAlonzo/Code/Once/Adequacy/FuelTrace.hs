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

module MAlonzo.Code.Once.Adequacy.FuelTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Metatheory.Trace
import qualified MAlonzo.Code.Once.Spec.Delay
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.FuelTrace.Obs
d_Obs_6 :: ()
d_Obs_6 = erased
-- Once.Adequacy.FuelTrace._⊕_
d__'8853'__8 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8853'__8 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Adequacy.FuelTrace._≼_
d__'8828'__14 a0 a1 = ()
data T__'8828'__14
  = C_'8828''45'cut_22 [MAlonzo.Code.Once.Spec.Signature.T_Event_246] |
    C_'8828''45'end_28
-- Once.Adequacy.FuelTrace.cutAt
d_cutAt_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cutAt_30 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v3 of
                       [] -> coe v1
                       (:) v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_cutAt_30 (coe v2)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                          (coe v4)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    d_cutAt_30 (coe v2)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v4))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.IsJust
d_IsJust_46 :: Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 -> ()
d_IsJust_46 = erased
-- Once.Adequacy.FuelTrace.Det
d_Det_48 :: Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Det_48 = erased
-- Once.Adequacy.FuelTrace.Det-ended
d_Det'45'ended_70 ::
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> AgdaAny
d_Det'45'ended_70 v0 v1 ~v2 = du_Det'45'ended_70 v0 v1
du_Det'45'ended_70 ::
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] -> AgdaAny
du_Det'45'ended_70 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                (:) v3 v4 -> coe du_Det'45'ended_70 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.≼-det
d_'8828''45'det_94 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T__'8828'__14 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8828''45'det_94 v0 v1 v2 v3 v4
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                C_'8828''45'cut_22 v7
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v9 of
                                     (:) v13 v14
                                       -> coe
                                            d_'8828''45'det_94 (coe v5)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe v14) (coe v7))
                                               (coe v12))
                                            (coe C_'8828''45'cut_22 v7) (coe v4)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_'8828''45'end_28
                  -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.≼-ended
d_'8828''45'ended_150 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T__'8828'__14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8828''45'ended_150 = erased
-- Once.Adequacy.FuelTrace.ended-≼
d_ended'45''8828'_162 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8828'__14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ended'45''8828'_162 = erased
-- Once.Adequacy.FuelTrace.⊕-≼
d_'8853''45''8828'_176 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T__'8828'__14 -> T__'8828'__14
d_'8853''45''8828'_176 ~v0 ~v1 ~v2 v3 = du_'8853''45''8828'_176 v3
du_'8853''45''8828'_176 :: T__'8828'__14 -> T__'8828'__14
du_'8853''45''8828'_176 v0 = coe v0
-- Once.Adequacy.FuelTrace._.assoc
d_assoc_196 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_196 = erased
-- Once.Adequacy.FuelTrace.bot-≼
d_bot'45''8828'_222 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T__'8828'__14
d_bot'45''8828'_222 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe C_'8828''45'cut_22 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.⇓-step
d_'8659''45'step_236 ::
  () ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_'8659''45'step_236 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8659''45'step_236 v5
du_'8659''45'step_236 ::
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_'8659''45'step_236 v0 = coe v0
-- Once.Adequacy.FuelTrace.Fuel._.go
d_go_256 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_go_256 ~v0 v1 = du_go_256 v1
du_go_256 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_go_256 v0
  = coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_go_52 (coe v0)
-- Once.Adequacy.FuelTrace.Fuel._.tr
d_tr_258 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_tr_258 ~v0 v1 = du_tr_258 v1
du_tr_258 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_tr_258 v0
  = coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_tr_50 (coe v0)
-- Once.Adequacy.FuelTrace.Fuel.runN
d_runN_262 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_262 ~v0 v1 v2 v3 = du_runN_262 v1 v2 v3
du_runN_262 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_262 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (coe du_runS_264 (coe v0) (coe v3) (coe v0 v2))
-- Once.Adequacy.FuelTrace.Fuel.runS
d_runS_264 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_264 ~v0 v1 v2 v3 = du_runS_264 v1 v2 v3
du_runS_264 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_264 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12 v3
        -> coe du_runN_262 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14 v3 v4
        -> coe
             d__'8853'__8 (coe v3) (coe du_runN_262 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4))
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stuck_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Fuel.runN-mono
d_runN'45'mono_296 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runN'45'mono_296 ~v0 v1 v2 v3 v4 v5
  = du_runN'45'mono_296 v1 v2 v3 v4 v5
du_runN'45'mono_296 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runN'45'mono_296 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             d_bot'45''8828'_222 (coe du_runN_262 (coe v0) (coe v2) (coe v3))
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                     -> coe
                          du_runS'45'mono_304 (coe v0) (coe v5) (coe v6) (coe v0 v3) (coe v9)
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.FuelTrace.Fuel.runS-mono
d_runS'45'mono_304 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runS'45'mono_304 ~v0 v1 v2 v3 v4 v5
  = du_runS'45'mono_304 v1 v2 v3 v4 v5
du_runS'45'mono_304 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runS'45'mono_304 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12 v5
        -> coe
             du_runN'45'mono_296 (coe v0) (coe v1) (coe v2) (coe v5) (coe v4)
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14 v5 v6
        -> coe
             du_runN'45'mono_296 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16 v5 v6
        -> coe C_'8828''45'end_28
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stuck_18
        -> coe
             C_'8828''45'cut_22
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Fuel.pre-listTr
d_pre'45'listTr_342 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'listTr_342 ~v0 ~v1 v2 v3 ~v4 = du_pre'45'listTr_342 v2 v3
du_pre'45'listTr_342 ::
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'listTr_342 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                []
                  -> coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                       (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v2))
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                       (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v2))
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe
                          MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Once.Spec.Delay.du_now_20
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
                          (coe du_pre'45'listTr_342 (coe v2) (coe v4))
                          (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.Fuel.pre-run
d_pre'45'run_368 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'run_368 ~v0 v1 v2 v3 v4 v5 v6
  = du_pre'45'run_368 v1 v2 v3 v4 v5 v6
du_pre'45'run_368 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'run_368 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                []
                  -> let v7 = subInt (coe v3) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_pre'45'go_376 (coe v0) (coe v6) (coe v7) (coe v0 v4) (coe v5))
                (:) v7 v8
                  -> coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                       (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v6))
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe
                          MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                          (coe
                             (\ v9 ->
                                coe
                                  MAlonzo.Code.Once.Spec.Delay.du_now_20
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))))
                          (coe
                             du_pre'45'run_368 (coe v0) (coe v6) (coe v8) (coe v3) (coe v4)
                             (coe v5))
                          (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.Fuel.pre-go
d_pre'45'go_376 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'go_376 ~v0 v1 v2 v3 v4 v5
  = du_pre'45'go_376 v1 v2 v3 v4 v5
du_pre'45'go_376 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'go_376 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12 v5
        -> coe
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42
             (coe
                MAlonzo.Code.Once.Metatheory.Trace.du_bindD_474
                (coe
                   MAlonzo.Code.Once.Adequacy.MachineTrace.du_go_52 (coe v0)
                   (coe v0 v5))
                (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1)))
             (coe
                du_pre'45'run_368 (coe v0)
                (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
                (coe v5) (coe v4))
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14 v5 v6
        -> case coe v5 of
             []
               -> coe
                    MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42
                    (coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bindD_474
                       (coe
                          MAlonzo.Code.Once.Adequacy.MachineTrace.du_go_52 (coe v0)
                          (coe v0 v6))
                       (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1)))
                    (coe
                       du_pre'45'run_368 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5) (coe v2)
                       (coe v6) (coe v4))
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                    (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                    (coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                       (coe
                          (\ v9 ->
                             coe
                               MAlonzo.Code.Once.Spec.Delay.du_now_20
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))))
                       (coe
                          du_pre'45'run_368 (coe v0) (coe v1) (coe v8) (coe v2) (coe v6)
                          (coe v4))
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16 v5 v6
        -> case coe v5 of
             []
               -> coe
                    MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                    (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                    (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                    (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                    (coe
                       MAlonzo.Code.Once.Metatheory.Trace.du_bind'8659'_574
                       (coe
                          (\ v9 ->
                             coe
                               MAlonzo.Code.Once.Spec.Delay.du_now_20
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))))
                       (coe du_pre'45'listTr_342 (coe v1) (coe v8))
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Fuel.inj₂-inj
d_inj'8322''45'inj_470 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_470 = erased
-- Once.Adequacy.FuelTrace.Fuel.clash
d_clash_482 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_clash_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_clash_482
du_clash_482 :: AgdaAny
du_clash_482 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Fuel.never-⇓
d_never'45''8659'_494 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8) ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_never'45''8659'_494 = erased
-- Once.Adequacy.FuelTrace.Fuel.run-pre
d_run'45'pre_526 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'pre_526 ~v0 v1 v2 v3 v4 v5 v6
  = du_run'45'pre_526 v1 v2 v3 v4 v5 v6
du_run'45'pre_526 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'pre_526 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                []
                  -> let v7
                           = coe
                               du_run'45'go_538 (coe v0) (coe v6) (coe v0 v3) (coe v4) (coe v5) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe
                                 seq (coe v9)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                (:) v7 v8
                  -> let v9
                           = coe
                               MAlonzo.Code.Once.Metatheory.Trace.du_at'8315'_650
                               (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v6))
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.MachineTrace.du_tr_50 (coe v0)
                                           (coe v8) (coe v3)))))
                               (coe v5) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> let v14
                                            = coe
                                                MAlonzo.Code.Once.Metatheory.Trace.du_at'8315'_650
                                                (coe
                                                   (\ v14 ->
                                                      coe
                                                        MAlonzo.Code.Once.Spec.Delay.du_now_20
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe v7)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                 (coe v14)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe v14)))))
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Delay.d_step_14
                                                   (coe
                                                      MAlonzo.Code.Once.Metatheory.Trace.du_pre_750
                                                      (coe v6)
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.MachineTrace.du_tr_50
                                                         (coe v0) (coe v8) (coe v3))))
                                                (coe v13) in
                                      coe
                                        (case coe v14 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                             -> case coe v16 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                    -> let v19
                                                             = coe
                                                                 du_run'45'pre_526 (coe v0) (coe v6)
                                                                 (coe v8) (coe v3) (coe v15)
                                                                 (coe v17) in
                                                       coe
                                                         (case coe v19 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                              -> case coe v21 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v20)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v22) erased)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.Fuel.run-go
d_run'45'go_538 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'go_538 ~v0 v1 v2 v3 ~v4 v5 ~v6 v7
  = du_run'45'go_538 v1 v2 v3 v5 v7
du_run'45'go_538 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'go_538 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v6 v8
               -> let v9
                        = coe
                            du_run'45'go_538 (coe v0) (coe v1) (coe v0 v5) (coe v3) (coe v8) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> coe
                              seq (coe v11)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14 v5 v6
        -> case coe v5 of
             []
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v7 v9
                      -> let v10
                               = coe
                                   du_run'45'go_538 (coe v0) (coe v1) (coe v0 v6) (coe v3)
                                   (coe v9) in
                         coe
                           (case coe v10 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             (:) v7 v8
               -> let v9
                        = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Once.Metatheory.Trace.du_at'8315'_650
                                  (coe MAlonzo.Code.Once.Metatheory.Trace.du_preStep_754 (coe v1))
                                  (coe v3)
                                  (coe
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                     (coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.MachineTrace.du_tr_50
                                              (coe v0) (coe v8) (coe v6)))))
                                  (coe v4))) in
                  coe
                    (let v10
                           = coe
                               MAlonzo.Code.Once.Metatheory.Trace.du_at'8315'_650
                               (coe
                                  (\ v10 ->
                                     coe
                                       MAlonzo.Code.Once.Spec.Delay.du_now_20
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))))
                               (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Spec.Delay.d_step_14
                                  (coe
                                     MAlonzo.Code.Once.Metatheory.Trace.du_pre_750 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.MachineTrace.du_tr_50 (coe v0)
                                        (coe v8) (coe v6))))
                               (coe v9) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> let v15
                                            = coe
                                                du_run'45'pre_526 (coe v0) (coe v1) (coe v8)
                                                (coe v6) (coe v11) (coe v13) in
                                      coe
                                        (case coe v15 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                             -> case coe v17 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                    -> let v20
                                                             = coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v16)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v18) erased) in
                                                       coe
                                                         (let v21
                                                                = coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v18) erased in
                                                          coe (coe seq (coe v21) (coe v20)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   du_Det'45'ended_70 (coe addInt (coe (1 :: Integer)) (coe v1))
                   (coe v5))
                erased)
      MAlonzo.Code.Once.Adequacy.MachineTrace.C_stuck_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Fuel._.q′
d_q'8242'_774 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'8242'_774 = erased
-- Once.Adequacy.FuelTrace.Fuel.align
d_align_830 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_align_830 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9
  = du_align_830 v1 v2 v3 v4 v5 v7 v9
du_align_830 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_align_830 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_pick_866 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      erased (coe v6)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_runN_262 (coe v0) (coe v4) (coe v2)))
      erased
-- Once.Adequacy.FuelTrace.Fuel._.viaMono
d_viaMono_850 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viaMono_850 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 v10
  = du_viaMono_850 v1 v2 v3 v4 v5 v7 v10
du_viaMono_850 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_viaMono_850 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_'8828''45'det_94 (coe v1)
      (coe du_runN_262 (coe v0) (coe v3) (coe v2))
      (coe du_runN_262 (coe v0) (coe v4) (coe v2))
      (coe
         du_runN'45'mono_296 (coe v0) (coe v3) (coe v4) (coe v2) (coe v6))
      (coe v5)
-- Once.Adequacy.FuelTrace.Fuel._.pick
d_pick_866 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pick_866 ~v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_pick_866 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11
du_pick_866 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pick_866 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> let v11
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     (\ v11 ->
                        coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                          (coe v3))
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v3) (coe v4))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v3)
                              (coe v4)))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                  -> if coe v12
                       then let v14
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                      (coe v13) in
                            coe
                              (coe
                                 du_viaMono_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe v5) (coe v14))
                       else coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_viaMono_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v7 v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Agree.F₁.align
d_align_904 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_align_904 ~v0 ~v1 v2 ~v3 = du_align_904 v2
du_align_904 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_align_904 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_align_830 (coe v0) v1 v2 v3 v4 v6 v8
-- Once.Adequacy.FuelTrace.Agree.F₁.pre-go
d_pre'45'go_906 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'go_906 ~v0 ~v1 v2 ~v3 = du_pre'45'go_906 v2
du_pre'45'go_906 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'go_906 v0 = coe du_pre'45'go_376 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.pre-listTr
d_pre'45'listTr_908 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'listTr_908 ~v0 ~v1 ~v2 ~v3 = du_pre'45'listTr_908
du_pre'45'listTr_908 ::
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'listTr_908 v0 v1 v2 = coe du_pre'45'listTr_342 v0 v1
-- Once.Adequacy.FuelTrace.Agree.F₁.pre-run
d_pre'45'run_910 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'run_910 ~v0 ~v1 v2 ~v3 = du_pre'45'run_910 v2
du_pre'45'run_910 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'run_910 v0 = coe du_pre'45'run_368 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.run-go
d_run'45'go_912 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'go_912 ~v0 ~v1 v2 ~v3 = du_run'45'go_912 v2
du_run'45'go_912 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'go_912 v0 v1 v2 v3 v4 v5 v6
  = coe du_run'45'go_538 (coe v0) v1 v2 v4 v6
-- Once.Adequacy.FuelTrace.Agree.F₁.run-pre
d_run'45'pre_914 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'pre_914 ~v0 ~v1 v2 ~v3 = du_run'45'pre_914 v2
du_run'45'pre_914 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'pre_914 v0 = coe du_run'45'pre_526 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.runN
d_runN_916 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_916 ~v0 ~v1 v2 ~v3 = du_runN_916 v2
du_runN_916 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_916 v0 = coe du_runN_262 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.runN-mono
d_runN'45'mono_918 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runN'45'mono_918 ~v0 ~v1 v2 ~v3 = du_runN'45'mono_918 v2
du_runN'45'mono_918 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runN'45'mono_918 v0 = coe du_runN'45'mono_296 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.runS
d_runS_920 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_920 ~v0 ~v1 v2 ~v3 = du_runS_920 v2
du_runS_920 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_920 v0 = coe du_runS_264 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₁.runS-mono
d_runS'45'mono_922 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runS'45'mono_922 ~v0 ~v1 v2 ~v3 = du_runS'45'mono_922 v2
du_runS'45'mono_922 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runS'45'mono_922 v0 = coe du_runS'45'mono_304 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.align
d_align_926 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_align_926 ~v0 ~v1 ~v2 v3 = du_align_926 v3
du_align_926 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_align_926 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_align_830 (coe v0) v1 v2 v3 v4 v6 v8
-- Once.Adequacy.FuelTrace.Agree.F₂.pre-go
d_pre'45'go_928 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'go_928 ~v0 ~v1 ~v2 v3 = du_pre'45'go_928 v3
du_pre'45'go_928 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'go_928 v0 = coe du_pre'45'go_376 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.pre-listTr
d_pre'45'listTr_930 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'listTr_930 ~v0 ~v1 ~v2 ~v3 = du_pre'45'listTr_930
du_pre'45'listTr_930 ::
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'listTr_930 v0 v1 v2 = coe du_pre'45'listTr_342 v0 v1
-- Once.Adequacy.FuelTrace.Agree.F₂.pre-run
d_pre'45'run_932 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
d_pre'45'run_932 ~v0 ~v1 ~v2 v3 = du_pre'45'run_932 v3
du_pre'45'run_932 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Spec.Delay.T__'8659'__30
du_pre'45'run_932 v0 = coe du_pre'45'run_368 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.run-go
d_run'45'go_934 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'go_934 ~v0 ~v1 ~v2 v3 = du_run'45'go_934 v3
du_run'45'go_934 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'go_934 v0 v1 v2 v3 v4 v5 v6
  = coe du_run'45'go_538 (coe v0) v1 v2 v4 v6
-- Once.Adequacy.FuelTrace.Agree.F₂.run-pre
d_run'45'pre_936 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'pre_936 ~v0 ~v1 ~v2 v3 = du_run'45'pre_936 v3
du_run'45'pre_936 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'pre_936 v0 = coe du_run'45'pre_526 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.runN
d_runN_938 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_938 ~v0 ~v1 ~v2 v3 = du_runN_938 v3
du_runN_938 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_938 v0 = coe du_runN_262 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.runN-mono
d_runN'45'mono_940 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runN'45'mono_940 ~v0 ~v1 ~v2 v3 = du_runN'45'mono_940 v3
du_runN'45'mono_940 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runN'45'mono_940 v0 = coe du_runN'45'mono_296 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.runS
d_runS_942 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_942 ~v0 ~v1 ~v2 v3 = du_runS_942 v3
du_runS_942 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_942 v0 = coe du_runS_264 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.F₂.runS-mono
d_runS'45'mono_944 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
d_runS'45'mono_944 ~v0 ~v1 ~v2 v3 = du_runS'45'mono_944 v3
du_runS'45'mono_944 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T__'8828'__14
du_runS'45'mono_944 v0 = coe du_runS'45'mono_304 (coe v0)
-- Once.Adequacy.FuelTrace.Agree._.trace
d_trace_948 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trace_948 ~v0 ~v1 v2 ~v3 = du_trace_948 v2
du_trace_948 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_trace_948 v0
  = coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80 (coe v0)
-- Once.Adequacy.FuelTrace.Agree._.trace
d_trace_952 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trace_952 ~v0 ~v1 ~v2 v3 = du_trace_952 v3
du_trace_952 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_trace_952 v0
  = coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80 (coe v0)
-- Once.Adequacy.FuelTrace.Agree.BudgetAgree
d_BudgetAgree_954 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny -> AgdaAny -> ()
d_BudgetAgree_954 = erased
-- Once.Adequacy.FuelTrace.Agree.endRefl
d_endRefl_968 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Metatheory.Trace.T_MaybeEnd_778
d_endRefl_968 ~v0 ~v1 ~v2 ~v3 v4 = du_endRefl_968 v4
du_endRefl_968 ::
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Metatheory.Trace.T_MaybeEnd_778
du_endRefl_968 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Trace.C_returned_12 v2
               -> coe
                    MAlonzo.Code.Once.Metatheory.Trace.C_end'8776'_790
                    (coe MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 erased)
             MAlonzo.Code.Once.Spec.Trace.C_halted_14
               -> coe
                    MAlonzo.Code.Once.Metatheory.Trace.C_end'8776'_790
                    (coe MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Metatheory.Trace.C_cut'8776'_784
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FuelTrace.Agree.obsRefl
d_obsRefl_974 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_obsRefl_974 ~v0 ~v1 ~v2 ~v3 v4 = du_obsRefl_974 v4
du_obsRefl_974 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_obsRefl_974 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         du_endRefl_968
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
-- Once.Adequacy.FuelTrace.Agree.agree-depth
d_agree'45'depth_982 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'depth_982 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_agree'45'depth_982 v2 v3 v4 v5 v6 v7
du_agree'45'depth_982 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'depth_982 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_fw_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe
         du_bw_1082 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Adequacy.FuelTrace.Agree._.fw
d_fw_1000 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fw_1000 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_fw_1000 v2 v3 v4 v5 v6 v7 v8 v9
du_fw_1000 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fw_1000 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              du_run'45'pre_526 (coe v0) (coe v5)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
              (coe v6) (coe v7) in
    coe
      (case coe v8 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
           -> case coe v10 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                  -> let v13 = coe v4 v9 in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> let v20
                                                   = coe
                                                       du_pick_866 (coe v0) (coe v5) (coe v2)
                                                       (coe v9) (coe v14) (coe v11) erased
                                                       (coe
                                                          (\ v20 ->
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe v19 v20)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             du_runN_262 (coe v0) (coe v14)
                                                             (coe v2)))
                                                       erased in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               du_pre'45'run_368 (coe v1) (coe v5)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                               (coe v16) (coe v3) (coe v21))
                                                            (coe du_obsRefl_974 (coe v6)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.Agree._._.q₂
d_q'8322'_1074 ::
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'8322'_1074 = erased
-- Once.Adequacy.FuelTrace.Agree._.bw
d_bw_1082 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bw_1082 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_bw_1082 v2 v3 v4 v5 v6 v7 v8 v9
du_bw_1082 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bw_1082 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              du_run'45'pre_526 (coe v1) (coe v5)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
              (coe v6) (coe v7) in
    coe
      (case coe v8 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
           -> case coe v10 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                  -> let v13 = coe v4 v9 in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> let v20
                                                   = coe
                                                       du_pick_866 (coe v1) (coe v5) (coe v3)
                                                       (coe v9) (coe v16) (coe v11) erased
                                                       (coe
                                                          (\ v20 ->
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe v19 erased)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             du_runN_262 (coe v1) (coe v16)
                                                             (coe v3)))
                                                       erased in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               du_pre'45'run_368 (coe v0) (coe v5)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                               (coe v14) (coe v2) (coe v21))
                                                            (coe du_obsRefl_974 (coe v6)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FuelTrace.Agree._._.q₁
d_q'8321'_1156 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q'8321'_1156 = erased
-- Once.Adequacy.FuelTrace.Agree.agree-≈
d_agree'45''8776'_1164 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_agree'45''8776'_1164 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_agree'45''8776'_1164 v2 v3 v4 v5 v6
du_agree'45''8776'_1164 ::
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  (AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8) ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_agree'45''8776'_1164 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Metatheory.Trace.du_fromDepth_1446
      (coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80 v0 v2)
      (coe MAlonzo.Code.Once.Adequacy.MachineTrace.du_trace_80 v1 v3)
      (coe
         du_agree'45'depth_982 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
