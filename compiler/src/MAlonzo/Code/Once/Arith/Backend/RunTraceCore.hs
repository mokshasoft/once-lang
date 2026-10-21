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

module MAlonzo.Code.Once.Arith.Backend.RunTraceCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Out
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Backend.RunTraceCore.RunTrace.ArithEnv
d_ArithEnv_32 ::
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
d_ArithEnv_32 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.EvExtractor
d_EvExtractor_34 ::
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
d_EvExtractor_34 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events
d_run'45'events_36 ::
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
d_run'45'events_36 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13 v14 v15 v16
  = du_run'45'events_36 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'events_36 ::
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
du_run'45'events_36 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      0 -> coe MAlonzo.Code.Once.Internal.Out.d_cut_8
      _ -> let v13 = subInt (coe v10) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v12)
                (coe MAlonzo.Code.Once.Internal.Out.d_stop_36)
                (coe
                   du_run'45'events'45'fetch_38 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v13)
                   (coe v11) (coe v12) (coe v2 v11 (coe v1 v12))))
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-fetch
d_run'45'events'45'fetch_38 ::
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
d_run'45'events'45'fetch_38 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                            v11 v12 v13 v14 v15 v16 v17
  = du_run'45'events'45'fetch_38
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_run'45'events'45'fetch_38 ::
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
du_run'45'events'45'fetch_38 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_run'45'events'45'instr_40 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v14) (coe v4 v14)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Internal.Out.d_stop_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-instr
d_run'45'events'45'instr_40 ::
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
d_run'45'events'45'instr_40 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                            v11 v12 v13 v14 v15 v16 v17 v18
  = du_run'45'events'45'instr_40
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_run'45'events'45'instr_40 ::
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
du_run'45'events'45'instr_40 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_run'45'events'45'site_44 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v15)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v15)
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_run'45'events'45'exec_48 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v3 v11 v12 v13)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-site
d_run'45'events'45'site_44 ::
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
d_run'45'events'45'site_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 v16 v17 v18
  = du_run'45'events'45'site_44
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_run'45'events'45'site_44 ::
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
du_run'45'events'45'site_44 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
        -> if coe v15
             then coe
                    seq (coe v16)
                    (coe
                       MAlonzo.Code.Once.Internal.Out.d_ended_10
                       (coe
                          MAlonzo.Code.Once.Spec.Trace.C_returned_12
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             else coe
                    seq (coe v16)
                    (coe
                       du_run'45'events'45'call_46 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe v11) (coe v12) (coe v13) (coe v8 v13))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-call
d_run'45'events'45'call_46 ::
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
d_run'45'events'45'call_46 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 v16 v17 v18
  = du_run'45'events'45'call_46
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_run'45'events'45'call_46 ::
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
du_run'45'events'45'call_46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v6 v15 v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Internal.Out.d__'9657'__14 (coe v7 v13 v12)
             (coe
                du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v9)
                   (coe v7 v13 v12))
                (coe v10) (coe v11) (coe v5 v9 v13 v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-exec
d_run'45'events'45'exec_48 ::
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
d_run'45'events'45'exec_48 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 ~v16 v17
  = du_run'45'events'45'exec_48
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v17
du_run'45'events'45'exec_48 ::
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
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'events'45'exec_48 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Internal.Out.d_stop_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-[]
d_run'45'events'45''91''93'_232 ::
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
  (Integer ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_232 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-noncall
d_run'45'events'45'noncall_492 ::
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
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'noncall_492 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-stuck
d_run'45'events'45'stuck_546 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_546 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-halted
d_run'45'events'45'halted_598 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_598 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-fetch-none
d_run'45'events'45'fetch'45'none_630 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_630 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace._.go
d_go_652 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_652 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-arith
d_run'45'events'45'arith_672 ::
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
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'arith_672 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-external
d_run'45'events'45'external_738 ::
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
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'external_738 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-leave
d_run'45'events'45'leave_800 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'leave_800 = erased
