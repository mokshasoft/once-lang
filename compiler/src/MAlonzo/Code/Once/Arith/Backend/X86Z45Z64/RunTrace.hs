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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceMachine
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Backend.X86-64.RunTrace.matchCall
d_matchCall_10 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_matchCall_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_54 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Once.Arith.Backend.X86-64.RunTrace.ret-past
d_ret'45'past_14 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384
d_ret'45'past_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_406
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_400
         (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
         (coe v0))
-- Once.Arith.Backend.X86-64.RunTrace.ret-with
d_ret'45'with_18 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384
d_ret'45'with_18 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_406
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_282
                     (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
                        (coe v2))
                     (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10) v1)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
                     (coe v2))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_400
                     (coe v2))
                  (coe
                     addInt (coe (1 :: Integer))
                     (coe
                        MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
                        (coe v2)))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
                     (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_406
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_396
                     (coe v1))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_398
                     (coe v1))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_400
                     (coe v1))
                  (coe
                     MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402 (coe v1))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.RunTrace.ret-call
d_ret'45'call_26 ::
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384
d_ret'45'call_26 v0 v1 v2 v3
  = coe d_ret'45'with_18 (coe v0 v1 v2 v3) v3
-- Once.Arith.Backend.X86-64.RunTrace._._.ArithEnv
d_ArithEnv_46 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  ()
d_ArithEnv_46 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.EvExtractor
d_EvExtractor_48 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  ()
d_EvExtractor_48 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events
d_run'45'events_50 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events_50 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-[]
d_run'45'events'45''91''93'_52 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_52 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-arith
d_run'45'events'45'arith_54 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'arith_54 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-call
d_run'45'events'45'call_56 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'call_56 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'call_46
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-exec
d_run'45'events'45'exec_58 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'exec_58 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'exec_48
      (coe
         (\ v9 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v9)))
      (coe
         (\ v9 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v9)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v9 v11))
      v2 v3 v4 v5 v6 v8
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-external
d_run'45'events'45'external_60 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'external_60 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-fetch
d_run'45'events'45'fetch_62 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'fetch_62 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'fetch_38
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-fetch-none
d_run'45'events'45'fetch'45'none_64 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_64 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-halted
d_run'45'events'45'halted_66 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_66 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-instr
d_run'45'events'45'instr_68 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'instr_68 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'instr_40
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-leave
d_run'45'events'45'leave_70 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'leave_70 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-noncall
d_run'45'events'45'noncall_72 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'noncall_72 = erased
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-site
d_run'45'events'45'site_74 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'events'45'site_74 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'site_44
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._._.run-events-stuck
d_run'45'events'45'stuck_76 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_76 = erased
-- Once.Arith.Backend.X86-64.RunTrace._.Run.Conf
d_Conf_80 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  ()
d_Conf_80 = erased
-- Once.Arith.Backend.X86-64.RunTrace._.Run.calls
d_calls_82 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
d_calls_82 ~v0 ~v1 = du_calls_82
du_calls_82 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
du_calls_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_calls_180 v3
-- Once.Arith.Backend.X86-64.RunTrace._.Run.ended-reaches
d_ended'45'reaches_84 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Reaches_82
d_ended'45'reaches_84 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_ended'45'reaches_590
      (coe
         (\ v11 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v11)))
      (coe
         (\ v11 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v11)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v11 v12 v13 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v11 v13))
      v2 v3 v4 v5 v6 v7 v9
-- Once.Arith.Backend.X86-64.RunTrace._.Run.outObs
d_outObs_86 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_outObs_86 ~v0 ~v1 = du_outObs_86
du_outObs_86 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_outObs_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_outObs_612 v3
-- Once.Arith.Backend.X86-64.RunTrace._.Run.runN-events
d_runN'45'events_88 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runN'45'events_88 = erased
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ
d_δ_90 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ_90 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ_92
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_404
              (coe v2)))
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-c
d_δ'45'c_92 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'c_92 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45'c_88
      (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v9 v11))
      v2 v5 v6 v7 v8
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-e
d_δ'45'e_94 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'e_94 ~v0 ~v1 = du_δ'45'e_94
du_δ'45'e_94 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Maybe
    MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
du_δ'45'e_94 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45'e_90 v3 v4
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-f
d_δ'45'f_96 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Maybe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'f_96 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45'f_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-h
d_δ'45'h_98 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  Bool ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'h_98 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45'h_78
      (coe
         (\ v2 ->
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_402
              (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_fetch_778)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_matchCall_10) (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-i
d_δ'45'i_100 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45'i_100 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45'i_82
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_execInstr_510)
      (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v2 v4))
-- Once.Arith.Backend.X86-64.RunTrace._.Run.δ-s
d_δ'45's_102 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   Maybe Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
   [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_30] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_384 ->
  MAlonzo.Code.Once.Adequacy.MachineTrace.T_Step_8
d_δ'45's_102 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceMachine.du_δ'45's_86
      (coe d_ret'45'call_26 (coe v1))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Dispatch.du_dispatch'45'arith_18
              (coe v0) v9 v11))
      v2 v3 v5 v6 v7 v8
