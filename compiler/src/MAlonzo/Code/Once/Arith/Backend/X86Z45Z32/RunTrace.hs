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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.RunTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.Arith.Backend.X86-32.RunTrace.matchCall
d_matchCall_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_matchCall_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.C_call'45'sym_52 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Once.Arith.Backend.X86-32.RunTrace.ret-past
d_ret'45'past_14 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268
d_ret'45'past_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.C_mkstate_290
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_280
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_282
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_flags_284
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
         (coe v0))
-- Once.Arith.Backend.X86-32.RunTrace._._.ArithEnv
d_ArithEnv_26 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  ()
d_ArithEnv_26 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.EvExtractor
d_EvExtractor_28 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  ()
d_EvExtractor_28 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events
d_run'45'events_30 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events_30 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-[]
d_run'45'events'45''91''93'_32 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_32 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-arith
d_run'45'events'45'arith_34 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'arith_34 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-call
d_run'45'events'45'call_36 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe
    [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'call_36 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'call_42
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-exec
d_run'45'events'45'exec_38 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'exec_38 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'exec_44
      (coe
         (\ v7 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v7)))
      (coe
         (\ v7 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v7)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
      v1 v2 v3 v4 v6
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-external
d_run'45'events'45'external_40 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'external_40 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-fetch
d_run'45'events'45'fetch_42 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'fetch_42 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'fetch_38
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-fetch-none
d_run'45'events'45'fetch'45'none_44 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_44 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-halted
d_run'45'events'45'halted_46 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_46 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-instr
d_run'45'events'45'instr_48 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'instr_48 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'instr_40
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-noncall
d_run'45'events'45'noncall_50 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'noncall_50 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-events-stuck
d_run'45'events'45'stuck_52 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_52 = erased
-- Once.Arith.Backend.X86-32.RunTrace._._.run-trace
d_run'45'trace_54 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe
     [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Syntax.T_Instr_26] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_268 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace_54 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_288
              (coe v1)))
      (coe
         (\ v1 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_286
              (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_fetch_622)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_execInstr_382)
      (coe d_matchCall_10) (coe d_ret'45'past_14)
      (coe
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Dispatch.d_dispatch'45'arith_16
         (coe v0))
