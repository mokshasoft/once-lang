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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Denotation.Trace

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
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
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
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
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
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'events_36 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13 v14 v15
  = du_run'45'events_36 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_run'45'events_36 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'events_36 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v12 = subInt (coe v9) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v11)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   du_run'45'events'45'fetch_38 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v12) (coe v10)
                   (coe v11) (coe v2 v10 (coe v1 v11))))
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
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'events'45'fetch_38 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                            v11 v12 v13 v14 v15 v16
  = du_run'45'events'45'fetch_38
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'events'45'fetch_38 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'events'45'fetch_38 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_run'45'events'45'instr_40 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v13) (coe v4 v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
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
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'events'45'instr_40 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                            v11 v12 v13 v14 v15 v16 v17
  = du_run'45'events'45'instr_40
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_run'45'events'45'instr_40 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'events'45'instr_40 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_run'45'events'45'call_42 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v14) (coe v8 v14)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_run'45'events'45'exec_44 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v3 v10 v11 v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-call
d_run'45'events'45'call_42 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'events'45'call_42 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 v16 v17
  = du_run'45'events'45'call_42
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_run'45'events'45'call_42 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'events'45'call_42 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v6 v14 v11)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7 v12 v11)
             (coe
                du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                (coe v5 v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-exec
d_run'45'events'45'exec_44 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'events'45'exec_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 ~v15 v16
  = du_run'45'events'45'exec_44
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v16
du_run'45'events'45'exec_44 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'events'45'exec_44 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-trace
d_run'45'trace_162 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_run'45'trace_162 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13 v14 v15 v16
  = du_run'45'trace_162 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'trace_162 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_run'45'trace_162 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v12)
      (coe
         du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v8) (coe v9) (coe v7 v12) (coe v10)
         (coe v11))
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-[]
d_run'45'events'45''91''93'_194 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  (Integer ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_194 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-noncall
d_run'45'events'45'noncall_390 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
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
d_run'45'events'45'noncall_390 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-stuck
d_run'45'events'45'stuck_440 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_440 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-halted
d_run'45'events'45'halted_488 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_488 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-fetch-none
d_run'45'events'45'fetch'45'none_516 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_516 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace._.go
d_go_536 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_536 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-arith
d_run'45'events'45'arith_554 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'arith_554 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-external
d_run'45'events'45'external_610 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'external_610 = erased
