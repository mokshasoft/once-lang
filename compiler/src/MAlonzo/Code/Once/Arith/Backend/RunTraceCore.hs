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
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Denotation.Behavior
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events_36 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13 v14 v15 v16
  = du_run'45'events_36 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'events_36 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events_36 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v13 = subInt (coe v10) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v12)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'fetch_38 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_run'45'events'45'instr_40 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v14) (coe v4 v14)
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'instr_40 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_run'45'events'45'call_42 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v15) (coe v8 v15)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_run'45'events'45'exec_44 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v3 v11 v12 v13)
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'call_42 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 v16 v17 v18
  = du_run'45'events'45'call_42
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
du_run'45'events'45'call_42 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'call_42 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v6 v15 v12)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7 v13 v12)
             (coe
                du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v9)
                   (coe v7 v13 v12))
                (coe v10) (coe v11) (coe v5 v9 v13 v12))
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
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'exec_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                           v11 v12 v13 v14 v15 ~v16 v17
  = du_run'45'events'45'exec_44
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v17
du_run'45'events'45'exec_44 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'exec_44 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
        -> coe
             du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v13)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-trace-fam
d_run'45'trace'45'fam_182 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'trace'45'fam_182 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                          v12 v13 v14 v15 v16
  = du_run'45'trace'45'fam_182
      v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'trace'45'fam_182 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'trace'45'fam_182 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v12)
      (coe
         du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v8) (coe v9)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7 v12)
         (coe v10) (coe v11))
-- Once.Arith.Backend.RunTraceCore.RunTrace.Adequate
d_Adequate_198 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
newtype T_Adequate_198
  = C_constructor_222 (Integer ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Arith.Backend.RunTraceCore.RunTrace.Adequate.extends
d_extends_216 ::
  T_Adequate_198 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extends_216 v0
  = case coe v0 of
      C_constructor_222 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.RunTraceCore.RunTrace.Adequate.saturates
d_saturates_220 ::
  T_Adequate_198 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_saturates_220 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-trace
d_run'45'trace_234 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_Adequate_198 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace_234 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13 v14 v15 v16
  = du_run'45'trace_234 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_run'45'trace_234 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_Adequate_198 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_run'45'trace_234 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.C_mkBehavior_40
      (coe
         du_run'45'trace'45'fam_182 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
         (coe v11))
      (d_extends_216 (coe v12))
      (coe
         du_bnd_254 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Arith.Backend.RunTraceCore.RunTrace._.bnd
d_bnd_254 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_Adequate_198 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_254 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          ~v16 v17
  = du_bnd_254 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v17
du_bnd_254 ::
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd_254 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe v12)
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268
         (coe
            du_run'45'events_36 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v6) (coe v8) (coe v9)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7 v12)
            (coe v10) (coe v11)))
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-[]
d_run'45'events'45''91''93'_280 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  AgdaAny ->
  (Integer ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_280 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-noncall
d_run'45'events'45'noncall_500 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'noncall_500 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-stuck
d_run'45'events'45'stuck_554 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_554 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-halted
d_run'45'events'45'halted_606 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_606 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-fetch-none
d_run'45'events'45'fetch'45'none_638 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_638 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace._.go
d_go_660 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_660 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-arith
d_run'45'events'45'arith_680 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'arith_680 = erased
-- Once.Arith.Backend.RunTraceCore.RunTrace.run-events-external
d_run'45'events'45'external_740 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> Bool) ->
  (AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'external_740 = erased
