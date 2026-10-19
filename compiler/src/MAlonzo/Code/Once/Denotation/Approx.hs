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

module MAlonzo.Code.Once.Denotation.Approx where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Denotation.Approx.Ap
d_Ap_8 a0 = ()
data T_Ap_8 = C_done_12 AgdaAny Integer | C_cut_14
-- Once.Denotation.Approx.approx
d_approx_18 ::
  () ->
  Integer ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_approx_18 ~v0 v1 v2 = du_approx_18 v1 v2
du_approx_18 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
du_approx_18 v0 v1
  = coe
      du_approxBlock_22 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v1))
-- Once.Denotation.Approx.approxBlock
d_approxBlock_22 ::
  () ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_approxBlock_22 ~v0 v1 v2 = du_approxBlock_22 v1 v2
du_approxBlock_22 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
du_approxBlock_22 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114
                    (coe C_done_12 (coe v3) (coe v0))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> case coe v0 of
                    0 -> coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe C_cut_14)
                    _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                         coe (coe du_approx_18 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Trace.C_call_118 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_approxBlock_22 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.Lang.Trace.C_halt_122 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Approx.NotCut
d_NotCut_56 :: () -> MAlonzo.Code.Once.Lang.Res.T_Res_8 -> ()
d_NotCut_56 = erased
-- Once.Denotation.Approx.budgetLeft
d_budgetLeft_60 ::
  () -> Integer -> MAlonzo.Code.Once.Lang.Res.T_Res_8 -> Integer
d_budgetLeft_60 ~v0 v1 v2 = du_budgetLeft_60 v1 v2
du_budgetLeft_60 ::
  Integer -> MAlonzo.Code.Once.Lang.Res.T_Res_8 -> Integer
du_budgetLeft_60 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12 -> coe v0
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v2
        -> case coe v2 of
             C_done_12 v3 v4 -> coe v4
             C_cut_14 -> coe (0 :: Integer)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Approx.tagRun
d_tagRun_72 ::
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tagRun_72 ~v0 v1 v2 = du_tagRun_72 v1 v2
du_tagRun_72 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tagRun_72 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Res.du_mapRes_24
         (coe (\ v2 -> coe C_done_12 (coe v2) (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
-- Once.Denotation.Approx.run-approx-embedB
d_run'45'approx'45'embedB_90 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'embedB_90 = erased
-- Once.Denotation.Approx.run-approx-call
d_run'45'approx'45'call_110 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'call_110 = erased
-- Once.Denotation.Approx.run-approx-embed
d_run'45'approx'45'embed_178 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'embed_178 = erased
-- Once.Denotation.Approx.is-stopped-tag
d_is'45'stopped'45'tag_196 ::
  () ->
  Integer ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_is'45'stopped'45'tag_196 = erased
-- Once.Denotation.Approx.budgetLeft-tag
d_budgetLeft'45'tag_210 ::
  () ->
  Integer ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_budgetLeft'45'tag_210 = erased
-- Once.Denotation.Approx.notCut-tag
d_notCut'45'tag_224 ::
  () -> Integer -> MAlonzo.Code.Once.Lang.Res.T_Res_8 -> AgdaAny
d_notCut'45'tag_224 ~v0 ~v1 v2 = du_notCut'45'tag_224 v2
du_notCut'45'tag_224 ::
  MAlonzo.Code.Once.Lang.Res.T_Res_8 -> AgdaAny
du_notCut'45'tag_224 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.Approx.done-tag
d_done'45'tag_242 ::
  () ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_done'45'tag_242 = erased
-- Once.Denotation.Approx.thenAp
d_thenAp_250 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thenAp_250 ~v0 ~v1 v2 v3 v4 v5 v6 = du_thenAp_250 v2 v3 v4 v5 v6
du_thenAp_250 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thenAp_250 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v5
        -> case coe v5 of
             C_done_12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du_appE_286 (coe v2)
                    (coe
                       MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
                       (coe du_approx_18 (coe v7) (coe v4 v6)))
             C_cut_14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Approx.run-approx-bindB
d_run'45'approx'45'bindB_294 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'bindB_294 = erased
-- Once.Denotation.Approx.run-approx-bind-call
d_run'45'approx'45'bind'45'call_322 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'bind'45'call_322 = erased
-- Once.Denotation.Approx.cons-thenAp
d_cons'45'thenAp_340 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'thenAp_340 = erased
-- Once.Denotation.Approx.run-approx-bind
d_run'45'approx'45'bind_478 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'bind_478 = erased
-- Once.Denotation.Approx.thenIter
d_thenIter_494 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thenIter_494 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_thenIter_494 v2 v3 v4 v5 v6
du_thenIter_494 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thenIter_494 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v5
        -> case coe v5 of
             C_done_12 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Lang.Res.C_returns_14
                              (coe C_done_12 (coe v8) (coe v7)))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v7 of
                           0 -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                  (coe MAlonzo.Code.Once.Lang.Res.C_returns_14 (coe C_cut_14))
                           _ -> let v9 = subInt (coe v7) (coe (1 :: Integer)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Once.Lang.Trace.du_appE_286 (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Trace.du_run_342 (coe v0)
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                                           (coe v2))
                                        (coe
                                           du_approx_18 (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Iterative.du_iterRun_212
                                              (coe v4) (coe v4 v8)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_cut_14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Approx.run-approx-iterB
d_run'45'approx'45'iterB_560 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'iterB_560 = erased
-- Once.Denotation.Approx.run-approx-iter-call
d_run'45'approx'45'iter'45'call_588 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'iter'45'call_588 = erased
-- Once.Denotation.Approx.cons-thenIter
d_cons'45'thenIter_606 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'thenIter_606 = erased
-- Once.Denotation.Approx.run-approx-iter
d_run'45'approx'45'iter_788 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'approx'45'iter_788 = erased
-- Once.Denotation.Approx.done-value
d_done'45'value_810 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_done'45'value_810 = erased
-- Once.Denotation.Approx.endAp
d_endAp_814 ::
  () ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8
d_endAp_814 ~v0 v1 = du_endAp_814 v1
du_endAp_814 ::
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_End_8
du_endAp_814 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Spec.Trace.C_halted_14)
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v1
        -> case coe v1 of
             C_done_12 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.Spec.Trace.C_returned_12
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             C_cut_14 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
