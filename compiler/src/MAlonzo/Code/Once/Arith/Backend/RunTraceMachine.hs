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

module MAlonzo.Code.Once.Arith.Backend.RunTraceMachine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.FuelTrace
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Backend.RunTraceMachine.RunMachine._.ArithEnv
d_ArithEnv_34 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_ArithEnv_34 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.EvExtractor
d_EvExtractor_36 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_EvExtractor_36 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events
d_run'45'events_38 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events_38 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events_38 v4 v5 v6 v7 v8 v9 v10
du_run'45'events_38 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events_38 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events-call
d_run'45'events'45'call_44 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'call_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events'45'call_44 v4 v5 v6 v7 v8 v9 v10
du_run'45'events'45'call_44 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'call_44 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'call_46
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events-exec
d_run'45'events'45'exec_46 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'exec_46 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events'45'exec_46 v4 v5 v6 v7 v8 v9 v10
du_run'45'events'45'exec_46 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'exec_46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'exec_48
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) v7
      v8 v9 v10 v11 v13
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events-fetch
d_run'45'events'45'fetch_50 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'fetch_50 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events'45'fetch_50 v4 v5 v6 v7 v8 v9 v10
du_run'45'events'45'fetch_50 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'fetch_50 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'fetch_38
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events-instr
d_run'45'events'45'instr_56 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'instr_56 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events'45'instr_56 v4 v5 v6 v7 v8 v9 v10
du_run'45'events'45'instr_56 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'instr_56 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'instr_40
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.run-events-site
d_run'45'events'45'site_62 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'site_62 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_run'45'events'45'site_62 v4 v5 v6 v7 v8 v9 v10
du_run'45'events'45'site_62 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'site_62 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'site_44
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Arith.Backend.RunTraceMachine.RunMachine.Conf
d_Conf_66 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Conf_66 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-h
d_δ'45'h_78 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Bool ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'h_78 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
            v15 v16
  = du_δ'45'h_78 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_δ'45'h_78 ::
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Bool ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'h_78 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = if coe v9
      then coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      else coe
             du_δ'45'f_80 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
             (coe v8) (coe v1 v8 (coe v0 v11)) (coe v10) (coe v11)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-f
d_δ'45'f_80 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'f_80 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12 v13
            v14 v15 v16
  = du_δ'45'f_80 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_δ'45'f_80 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'f_80 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             du_δ'45'i_82 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe v10) (coe v1 v10) (coe v8) (coe v9)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-i
d_δ'45'i_82 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'i_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10 v11 v12 v13
            v14 v15 v16 v17
  = du_δ'45'i_82 v7 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_δ'45'i_82 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'i_82 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             du_δ'45's_86 (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v10)
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
             (coe v8) (coe v9)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_δ'45'e_90 (coe v0 v5 v9 v6) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-s
d_δ'45's_86 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45's_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12 ~v13
            v14 v15 v16 v17
  = du_δ'45's_86 v9 v10 v11 v12 v14 v15 v16 v17
du_δ'45's_86 ::
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45's_86 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                       (coe
                          MAlonzo.Code.Once.Spec.Trace.C_returned_12
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             else coe
                    seq (coe v9)
                    (coe
                       du_δ'45'c_88 (coe v0) (coe v1) (coe v2) (coe v4) (coe v3 v4)
                       (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-c
d_δ'45'c_88 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'c_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12
            ~v13 v14 v15 v16 v17
  = du_δ'45'c_88 v9 v10 v11 v14 v15 v16 v17
du_δ'45'c_88 ::
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'c_88 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                (coe v1 v7 v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_emit_14
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
                (coe v2 v3 v6))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                   (coe v2 v3 v6))
                (coe v0 v5 v3 v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ-e
d_δ'45'e_90 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'e_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 v15
  = du_δ'45'e_90 v14 v15
du_δ'45'e_90 ::
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'e_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_silent_12
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_stop_16
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.δ
d_δ_92 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ_92 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du_δ_92 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_δ_92 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ_92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
        -> coe
             du_δ'45'h_78 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe v7) (coe v8) (coe v9) (coe v0 v12) (coe v11) (coe v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._._.Reaches
d_Reaches_164 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
              a16
  = ()
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.calls
d_calls_180 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
d_calls_180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14
  = du_calls_180 v14
du_calls_180 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
du_calls_180 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach
d_reach_192 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach_192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
            v15 v16 v17 ~v18
  = du_reach_192 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_reach_192 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach_192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = let v14 = subInt (coe v10) (coe (1 :: Integer)) in
    coe
      (coe
         du_reach'45'h_204 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14) (coe v11)
         (coe v12) (coe v0 v12) (coe v13))
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-h
d_reach'45'h_204 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45'h_204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 ~v18 v19 ~v20
  = du_reach'45'h_204
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19
du_reach'45'h_204 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45'h_204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = if coe v13
      then coe du_stopAt_302
      else coe
             du_reach'45'f_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v2 v9 (coe v1 v12)) (coe v14)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-f
d_reach'45'f_216 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45'f_216 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 ~v18 ~v19 v20 ~v21
  = du_reach'45'f_216
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v20
du_reach'45'f_216 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45'f_216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_reach'45'i_230 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v15) (coe v4 v15) (coe v14)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe du_stopAt_302
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-i
d_reach'45'i_230 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45'i_230 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_reach'45'i_230
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v22
du_reach'45'i_230 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45'i_230 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
        -> coe
             du_reach'45's_246 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v16)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v16)
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
             (coe v15)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_reach'45'e_278 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v3 v9 v12 v13) (coe v15)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-s
d_reach'45's_246 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45's_246 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_reach'45's_246
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v18 v19 v24
du_reach'45's_246 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45's_246 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v14 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
        -> if coe v16
             then coe seq (coe v17) (coe du_stopAt_302)
             else coe
                    seq (coe v17)
                    (coe
                       du_reach'45'c_264 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v13) (coe v8 v13) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-c
d_reach'45'c_264 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45'c_264 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 ~v17 v18 v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26 ~v27
  = du_reach'45'c_264
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v18 v19 v26
du_reach'45'c_264 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45'c_264 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'silent_92
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                (coe v6 v16 v12))
             (coe
                du_reach_192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                (coe v6 v16 v12) (coe v15))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'emit_104
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v11)
                   (coe v7 v13 v12))
                (coe v5 v11 v13 v12))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
                (coe v7 v13 v12))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Internal.Event.d_toEvent_164)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v11)
                         (coe v7 v13 v12))
                      (coe v10) (coe v9) (coe v5 v11 v13 v12))))
             (coe
                du_reach_192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v11)
                   (coe v7 v13 v12))
                (coe v5 v11 v13 v12) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.reach-e
d_reach'45'e_278 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_reach'45'e_278 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24
  = du_reach'45'e_278
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v18 v23
du_reach'45'e_278 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Maybe AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_reach'45'e_278 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'silent_92
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) (coe v14))
             (coe
                du_reach_192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14)
                (coe v13))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe du_stopAt_302
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.stopAt
d_stopAt_302 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_stopAt_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_stopAt_302
du_stopAt_302 ::
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_stopAt_302
  = coe MAlonzo.Code.Once.Adequacy.MachineTrace.C_r'45'stop_112
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.ended-reaches
d_ended'45'reaches_590 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_ended'45'reaches_590 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                       v12 v13 v14 v15 v16 ~v17 v18 ~v19
  = du_ended'45'reaches_590
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v18
du_ended'45'reaches_590 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
du_ended'45'reaches_590 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13
  = coe
      du_reach_192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13)
-- Once.Arith.Backend.RunTraceMachine.RunMachine._._.runN
d_runN_608 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runN_608 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_runN_608 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_runN_608 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runN_608 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runN_262
      (coe
         du_δ_92 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Arith.Backend.RunTraceMachine.RunMachine._._.runS
d_runS_610 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_runS_610 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_runS_610 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_runS_610 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_runS_610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.FuelTrace.du_runS_264
      (coe
         du_δ_92 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9))
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.outObs
d_outObs_612 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_outObs_612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 v14
  = du_outObs_612 v14
du_outObs_612 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_outObs_612 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_calls_180 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.runN-events
d_runN'45'events_622 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runN'45'events_622 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-h
d_rn'45'h_632 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45'h_632 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-f
d_rn'45'f_642 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45'f_642 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-i
d_rn'45'i_654 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45'i_654 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-s
d_rn'45's_666 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45's_666 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-c
d_rn'45'c_678 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45'c_678 = erased
-- Once.Arith.Backend.RunTraceMachine.RunMachine._.rn-e
d_rn'45'e_688 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rn'45'e_688 = erased
