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

module MAlonzo.Code.Once.Adequacy.MachineTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Delay
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Adequacy.MachineTrace.Step
d_Step_8 a0 = ()
data T_Step_8
  = C_silent_12 AgdaAny |
    C_emit_14 [MAlonzo.Code.Once.Spec.Signature.T_Event_246] AgdaAny |
    C_stop_16 [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
              MAlonzo.Code.Once.Spec.Trace.T_End_8 |
    C_stuck_18
-- Once.Adequacy.MachineTrace.listTr
d_listTr_20 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_listTr_20 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_26
      (coe
         MAlonzo.Code.Once.Spec.Delay.C_constructor_16
         (case coe v0 of
            []
              -> coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
            (:) v2 v3
              -> coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                   (coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                         (coe d_listTr_20 (coe v3) (coe v1))))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.MachineTrace.never
d_never_32 :: () -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_never_32 ~v0 = du_never_32
du_never_32 :: MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_never_32
  = coe
      MAlonzo.Code.Once.Spec.Delay.C_constructor_16
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_never_32))
-- Once.Adequacy.MachineTrace.silentTr
d_silentTr_34 :: MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_silentTr_34
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_26 (coe du_never_32)
-- Once.Adequacy.MachineTrace.S′
d_S'8242'_36 :: ()
d_S'8242'_36 = erased
-- Once.Adequacy.MachineTrace.endRefl
d_endRefl_40 ::
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Once.Spec.Trace.T_EndRel_32
d_endRefl_40 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Trace.C_returned_12 v1
        -> coe MAlonzo.Code.Once.Spec.Trace.C_returned'8776'_42 erased
      MAlonzo.Code.Once.Spec.Trace.C_halted_14
        -> coe MAlonzo.Code.Once.Spec.Trace.C_halted'8776'_44
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.tr
d_tr_50 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_tr_50 ~v0 v1 v2 v3 = du_tr_50 v1 v2 v3
du_tr_50 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_tr_50 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_26
      (case coe v1 of
         [] -> coe du_go_52 (coe v0) (coe v0 v2)
         (:) v3 v4
           -> coe
                MAlonzo.Code.Once.Spec.Delay.C_constructor_16
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                   (coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                         (coe du_tr_50 (coe v0) (coe v4) (coe v2)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MachineTrace.Machine.go
d_go_52 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  T_Step_8 -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8
d_go_52 ~v0 v1 v2 = du_go_52 v1 v2
du_go_52 ::
  (AgdaAny -> T_Step_8) ->
  T_Step_8 -> MAlonzo.Code.Once.Spec.Delay.T_Delay_8
du_go_52 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Delay.C_constructor_16
      (case coe v1 of
         C_silent_12 v2
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe du_go_52 (coe v0) (coe v0 v2))
         C_emit_14 v2 v3
           -> case coe v2 of
                []
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_go_52 (coe v0) (coe v0 v3))
                (:) v4 v5
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe du_tr_50 (coe v0) (coe v5) (coe v3))))
                _ -> MAlonzo.RTE.mazUnreachableError
         C_stop_16 v2 v3
           -> case coe v2 of
                []
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3))
                (:) v4 v5
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe d_listTr_20 (coe v5) (coe v3))))
                _ -> MAlonzo.RTE.mazUnreachableError
         C_stuck_18
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_never_32)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MachineTrace.Machine.trace
d_trace_80 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trace_80 ~v0 v1 = du_trace_80 v1
du_trace_80 ::
  (AgdaAny -> T_Step_8) ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_trace_80 v0
  = coe
      du_tr_50 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.MachineTrace.Machine.Reaches
d_Reaches_82 a0 a1 a2 a3 a4 = ()
data T_Reaches_82
  = C_r'45'silent_92 AgdaAny T_Reaches_82 |
    C_r'45'emit_104 AgdaAny
                    [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
                    [MAlonzo.Code.Once.Spec.Signature.T_Event_246] T_Reaches_82 |
    C_r'45'stop_112
-- Once.Adequacy.MachineTrace.Machine.Good
d_Good_114 a0 a1 a2 a3 a4 = ()
data T_Good_114
  = C_g'45'run_126 [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
                   AgdaAny [MAlonzo.Code.Once.Spec.Signature.T_Event_246]
                   T_Reaches_82 |
    C_g'45'fin_132
-- Once.Adequacy.MachineTrace.Machine.Arrive
d_Arrive_134 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> ()
d_Arrive_134 = erased
-- Once.Adequacy.MachineTrace.Machine.laterA
d_laterA_158 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_laterA_158 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 = du_laterA_158 v3 v4 v7
du_laterA_158 ::
  MAlonzo.Code.Once.Spec.Delay.T_Delay_8 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  AgdaAny -> AgdaAny
du_laterA_158 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v0 v2
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Spec.Delay.C_later'8659'_42 v0 v7) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.arriveR
d_arriveR_182 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> T_Reaches_82 -> AgdaAny
d_arriveR_182 ~v0 v1 ~v2 v3 v4 v5 = du_arriveR_182 v1 v3 v4 v5
du_arriveR_182 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> T_Reaches_82 -> AgdaAny
du_arriveR_182 v0 v1 v2 v3
  = case coe v3 of
      C_r'45'silent_92 v5 v9
        -> coe
             du_laterA_158 (coe du_go_52 (coe v0) (coe v0 v5)) (coe v1)
             (coe du_arriveR_182 (coe v0) (coe v1) (coe v2) (coe v9))
      C_r'45'emit_104 v5 v6 v7 v10
        -> case coe v6 of
             []
               -> coe
                    du_laterA_158 (coe du_go_52 (coe v0) (coe v0 v5)) (coe v7)
                    (coe du_arriveR_182 (coe v0) (coe v7) (coe v2) (coe v10))
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_tr_50 (coe v0) (coe v12) (coe v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe C_g'45'run_126 v12 v5 v7 v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_r'45'stop_112
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_listTr_20 (coe v9) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe C_g'45'fin_132))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.arriveG
d_arriveG_256 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> T_Good_114 -> AgdaAny
d_arriveG_256 ~v0 v1 ~v2 v3 v4 v5 = du_arriveG_256 v1 v3 v4 v5
du_arriveG_256 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> T_Good_114 -> AgdaAny
du_arriveG_256 v0 v1 v2 v3
  = case coe v3 of
      C_g'45'run_126 v4 v5 v6 v9
        -> case coe v4 of
             [] -> coe du_arriveR_182 (coe v0) (coe v1) (coe v2) (coe v9)
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_tr_50 (coe v0) (coe v12) (coe v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe C_g'45'run_126 v12 v5 v6 v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_g'45'fin_132
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_listTr_20 (coe v7) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                       (coe C_g'45'fin_132))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.endAt
d_endAt_282 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_endAt_282 ~v0 ~v1 v2 ~v3 ~v4 = du_endAt_282 v2
du_endAt_282 :: MAlonzo.Code.Once.Spec.Trace.T_End_8 -> AgdaAny
du_endAt_282 v0 = coe d_endRefl_40 (coe v0)
-- Once.Adequacy.MachineTrace.Machine.endAt′
d_endAt'8242'_294 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_endAt'8242'_294 ~v0 ~v1 v2 ~v3 ~v4 = du_endAt'8242'_294 v2
du_endAt'8242'_294 ::
  MAlonzo.Code.Once.Spec.Trace.T_End_8 -> AgdaAny
du_endAt'8242'_294 v0 = coe d_endRefl_40 (coe v0)
-- Once.Adequacy.MachineTrace.Machine.evAt
d_evAt_310 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  AgdaAny
d_evAt_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_evAt_310 v7
du_evAt_310 ::
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  AgdaAny
du_evAt_310 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v0)
-- Once.Adequacy.MachineTrace.Machine.evAt′
d_evAt'8242'_326 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Signature.T_Event_246 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  AgdaAny
d_evAt'8242'_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_evAt'8242'_326 v7
du_evAt'8242'_326 ::
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86 ->
  AgdaAny
du_evAt'8242'_326 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v0)
-- Once.Adequacy.MachineTrace.Machine.good-≈
d_good'45''8776'_336 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_good'45''8776'_336 ~v0 v1 ~v2 v3 v4 v5
  = du_good'45''8776'_336 v1 v3 v4 v5
du_good'45''8776'_336 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_good'45''8776'_336 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Trace.C_constructor_108
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (\ v4 v5 -> coe du_fwdG_352 (coe v0) (coe v1) (coe v2) (coe v3))
         (\ v4 v5 -> coe du_bwdG_368 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Adequacy.MachineTrace.Machine.fwdG
d_fwdG_352 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fwdG_352 ~v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_fwdG_352 v1 v3 v4 v5
du_fwdG_352 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fwdG_352 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                (coe du_endAt_282 (coe v2)))
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                   (coe d_listTr_20 (coe v5) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Spec.Delay.C_now'8659'_38)
                (coe
                   du_evAt_310
                   (coe
                      du_good'45''8776'_336 (coe v0) (coe v5) (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe du_arriveG_256 (coe v0) (coe v1) (coe v2) (coe v3)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.bwdG
d_bwdG_368 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Delay.T__'8659'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bwdG_368 ~v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_bwdG_368 v1 v3 v4 v5
du_bwdG_368 ::
  (AgdaAny -> T_Step_8) ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Good_114 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bwdG_368 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe du_arriveG_256 (coe v0) (coe v1) (coe v2) (coe v3))
                (coe du_endAt'8242'_294 (coe v2)))
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe du_arriveG_256 (coe v0) (coe v1) (coe v2) (coe v3)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_arriveG_256 (coe v0) (coe v1) (coe v2) (coe v3))))
                (coe
                   du_evAt'8242'_326
                   (coe
                      du_good'45''8776'_336 (coe v0) (coe v5) (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe du_arriveG_256 (coe v0) (coe v1) (coe v2) (coe v3)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MachineTrace.Machine.reaches-≈
d_reaches'45''8776'_426 ::
  () ->
  (AgdaAny -> T_Step_8) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Reaches_82 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_reaches'45''8776'_426 ~v0 v1 v2 v3 v4 v5
  = du_reaches'45''8776'_426 v1 v2 v3 v4 v5
du_reaches'45''8776'_426 ::
  (AgdaAny -> T_Step_8) ->
  AgdaAny ->
  [MAlonzo.Code.Once.Spec.Signature.T_Event_246] ->
  MAlonzo.Code.Once.Spec.Trace.T_End_8 ->
  T_Reaches_82 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_reaches'45''8776'_426 v0 v1 v2 v3 v4
  = coe
      du_good'45''8776'_336 (coe v0) (coe v2) (coe v3)
      (coe
         C_g'45'run_126 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         v1 v2 v4)
