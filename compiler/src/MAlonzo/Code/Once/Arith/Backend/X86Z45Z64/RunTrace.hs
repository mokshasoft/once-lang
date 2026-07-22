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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.RunTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Arith.Backend.X86-64.RunTrace.matchCall
d_matchCall_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_matchCall_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_50 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Once.Arith.Backend.X86-64.RunTrace.ret-past
d_ret'45'past_14 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_ret'45'past_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v0))
-- Once.Arith.Backend.X86-64.RunTrace._._.ArithEnv
d_ArithEnv_26 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ()
d_ArithEnv_26 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.EvExtractor
d_EvExtractor_28 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ()
d_EvExtractor_28 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events
d_run'45'events_30 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events_30 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v1 v3))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-call
d_run'45'events'45'call_32 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'call_32 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'call_42
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v1 v3))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-exec
d_run'45'events'45'exec_34 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'exec_34 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'exec_44
      (coe
         (\ v7 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v7)))
      (coe
         (\ v7 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v7)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v7 v9))
      v1 v2 v3 v4 v6
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-fetch
d_run'45'events'45'fetch_36 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'fetch_36 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'fetch_38
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v1 v3))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-instr
d_run'45'events'45'instr_38 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'instr_38 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'instr_40
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v1 v3))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-trace
d_run'45'trace_40 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace_40 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_554)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_332)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v1 v3))
