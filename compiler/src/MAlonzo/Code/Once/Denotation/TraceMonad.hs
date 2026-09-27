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

module MAlonzo.Code.Once.Denotation.TraceMonad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Res

-- Once.Denotation.TraceMonad.Stopped
d_Stopped_6 :: ()
d_Stopped_6 = erased
-- Once.Denotation.TraceMonad.T
d_T_10 a0 = ()
data T_T_10
  = C_mkT_22 (Integer ->
              [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120])
             MAlonzo.Code.Once.Res.T_Res_6
-- Once.Denotation.TraceMonad.T.trT
d_trT_18 ::
  T_T_10 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_trT_18 v0
  = case coe v0 of
      C_mkT_22 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.T.resT
d_resT_20 :: T_T_10 -> MAlonzo.Code.Once.Res.T_Res_6
d_resT_20 v0
  = case coe v0 of
      C_mkT_22 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.atT
d_atT_26 ::
  T_T_10 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atT_26 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_trT_18 v0 v1)
      (coe d_resT_20 (coe v0))
-- Once.Denotation.TraceMonad.returnT
d_returnT_34 :: () -> AgdaAny -> T_T_10
d_returnT_34 ~v0 v1 = du_returnT_34 v1
du_returnT_34 :: AgdaAny -> T_T_10
du_returnT_34 v0
  = coe
      C_mkT_22
      (coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe MAlonzo.Code.Once.Res.C_returns_12 (coe v0))
-- Once.Denotation.TraceMonad.resT-lift
d_resT'45'lift_42 :: MAlonzo.Code.Once.Res.T_Res_6 -> T_T_10
d_resT'45'lift_42 v0
  = coe
      C_mkT_22
      (coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v0)
-- Once.Denotation.TraceMonad.bindRes
d_bindRes_52 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> (AgdaAny -> T_T_10) -> T_T_10
d_bindRes_52 ~v0 ~v1 v2 v3 v4 = du_bindRes_52 v2 v3 v4
du_bindRes_52 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> (AgdaAny -> T_T_10) -> T_T_10
du_bindRes_52 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe C_mkT_22 (coe v0) (coe v1)
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe
             C_mkT_22
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0 v4)
                     (coe
                        d_trT_18 (coe v2 v3)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v4
                           (coe MAlonzo.Code.Data.List.Base.du_length_268 (coe v0 v4))))))
             (coe d_resT_20 (coe v2 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad._>>=T_
d__'62''62''61'T__70 ::
  () -> () -> T_T_10 -> (AgdaAny -> T_T_10) -> T_T_10
d__'62''62''61'T__70 ~v0 ~v1 v2 v3 = du__'62''62''61'T__70 v2 v3
du__'62''62''61'T__70 :: T_T_10 -> (AgdaAny -> T_T_10) -> T_T_10
du__'62''62''61'T__70 v0 v1
  = coe
      du_bindRes_52 (coe d_trT_18 (coe v0)) (coe d_resT_20 (coe v0))
      (coe v1)
-- Once.Denotation.TraceMonad._>>T_
d__'62''62'T__80 :: () -> () -> T_T_10 -> T_T_10 -> T_T_10
d__'62''62'T__80 ~v0 ~v1 v2 v3 = du__'62''62'T__80 v2 v3
du__'62''62'T__80 :: T_T_10 -> T_T_10 -> T_T_10
du__'62''62'T__80 v0 v1
  = coe du__'62''62''61'T__70 (coe v0) (coe (\ v2 -> v1))
-- Once.Denotation.TraceMonad.fmapT
d_fmapT_92 :: () -> () -> (AgdaAny -> AgdaAny) -> T_T_10 -> T_T_10
d_fmapT_92 ~v0 ~v1 v2 v3 = du_fmapT_92 v2 v3
du_fmapT_92 :: (AgdaAny -> AgdaAny) -> T_T_10 -> T_T_10
du_fmapT_92 v0 v1
  = coe
      C_mkT_22 (coe d_trT_18 (coe v1))
      (coe
         MAlonzo.Code.Once.Res.du_mapRes_46 (coe v0)
         (coe d_resT_20 (coe v1)))
-- Once.Denotation.TraceMonad.tell
d_tell_98 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] -> T_T_10
d_tell_98 v0
  = coe
      C_mkT_22
      (coe
         (\ v1 ->
            coe MAlonzo.Code.Data.List.Base.du_take_530 (coe v1) (coe v0)))
      (coe
         MAlonzo.Code.Once.Res.C_returns_12
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Denotation.TraceMonad.projTrace
d_projTrace_106 ::
  T_T_10 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_projTrace_106 v0 v1 = coe d_trT_18 v0 v1
-- Once.Denotation.TraceMonad.stoppedT
d_stoppedT_114 :: () -> T_T_10 -> Integer -> Bool
d_stoppedT_114 ~v0 v1 ~v2 = du_stoppedT_114 v1
du_stoppedT_114 :: T_T_10 -> Bool
du_stoppedT_114 v0
  = coe
      MAlonzo.Code.Once.Res.du_is'45'stopped_16 (coe d_resT_20 (coe v0))
-- Once.Denotation.TraceMonad.Returns?
d_Returns'63'_120 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_Returns'63'_120 = erased
-- Once.Denotation.TraceMonad.resVal
d_resVal_126 ::
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny -> AgdaAny
d_resVal_126 ~v0 v1 ~v2 = du_resVal_126 v1
du_resVal_126 :: MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_resVal_126 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.valueT
d_valueT_138 :: () -> T_T_10 -> Integer -> AgdaAny -> AgdaAny
d_valueT_138 ~v0 v1 ~v2 ~v3 = du_valueT_138 v1
du_valueT_138 :: T_T_10 -> AgdaAny
du_valueT_138 v0 = coe du_resVal_126 (coe d_resT_20 (coe v0))
-- Once.Denotation.TraceMonad.Returns?-of
d_Returns'63''45'of_150 ::
  () ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Returns'63''45'of_150 ~v0 v1 ~v2 = du_Returns'63''45'of_150 v1
du_Returns'63''45'of_150 ::
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_Returns'63''45'of_150 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.TraceMonad.resVal-returns
d_resVal'45'returns_158 ::
  () ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resVal'45'returns_158 = erased
-- Once.Denotation.TraceMonad.bindResAt
d_bindResAt_166 ::
  () ->
  () ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bindResAt_166 ~v0 ~v1 v2 v3 v4 v5 = du_bindResAt_166 v2 v3 v4 v5
du_bindResAt_166 ::
  (AgdaAny -> T_T_10) ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bindResAt_166 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Res.C_returns_12 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                (coe
                   d_trT_18 (coe v0 v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
             (coe d_resT_20 (coe v0 v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.bindAt
d_bindAt_186 ::
  () ->
  () ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bindAt_186 ~v0 ~v1 v2 v3 v4 = du_bindAt_186 v2 v3 v4
du_bindAt_186 ::
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bindAt_186 v0 v1 v2
  = coe
      du_bindResAt_166 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
-- Once.Denotation.TraceMonad.bindRes-at
d_bindRes'45'at_206 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'at_206 = erased
-- Once.Denotation.TraceMonad.>>=T-at
d_'62''62''61'T'45'at_232 ::
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'at_232 = erased
-- Once.Denotation.TraceMonad.>>=T-cong-at
d_'62''62''61'T'45'cong'45'at_252 ::
  () ->
  () ->
  T_T_10 ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'cong'45'at_252 = erased
-- Once.Denotation.TraceMonad.bindResAt-cong
d_bindResAt'45'cong_280 ::
  () ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindResAt'45'cong_280 = erased
-- Once.Denotation.TraceMonad.bindAt-cong
d_bindAt'45'cong_322 ::
  () ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindAt'45'cong_322 = erased
-- Once.Denotation.TraceMonad.>>=T-cong₂-at
d_'62''62''61'T'45'cong'8322''45'at_350 ::
  () ->
  () ->
  T_T_10 ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'cong'8322''45'at_350 = erased
-- Once.Denotation.TraceMonad.Bounded
d_Bounded_368 :: T_T_10 -> ()
d_Bounded_368 = erased
-- Once.Denotation.TraceMonad.Saturating
d_Saturating_376 :: T_T_10 -> ()
d_Saturating_376 = erased
-- Once.Denotation.TraceMonad.Coherent
d_Coherent_384 :: T_T_10 -> ()
d_Coherent_384 = erased
-- Once.Denotation.TraceMonad.PrefixFamily
d_PrefixFamily_396 a0 a1 = ()
data T_PrefixFamily_396
  = C_prefixFamily_414 (Integer ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Denotation.TraceMonad.PrefixFamily.bnd
d_bnd_408 ::
  T_PrefixFamily_396 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_408 v0
  = case coe v0 of
      C_prefixFamily_414 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.PrefixFamily.sat
d_sat_410 ::
  T_PrefixFamily_396 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_410 = erased
-- Once.Denotation.TraceMonad.PrefixFamily.coh
d_coh_412 ::
  T_PrefixFamily_396 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh_412 v0
  = case coe v0 of
      C_prefixFamily_414 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.returnT-pf
d_returnT'45'pf_420 :: () -> AgdaAny -> T_PrefixFamily_396
d_returnT'45'pf_420 ~v0 ~v1 = du_returnT'45'pf_420
du_returnT'45'pf_420 :: T_PrefixFamily_396
du_returnT'45'pf_420
  = coe
      C_prefixFamily_414
      (\ v0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased)
-- Once.Denotation.TraceMonad.length-take-≤
d_length'45'take'45''8804'_436 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'take'45''8804'_436 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (d_length'45'take'45''8804'_436 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad.take-sat
d_take'45'sat_446 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'sat_446 = erased
-- Once.Denotation.TraceMonad.take-coh
d_take'45'coh_464 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_take'45'coh_464 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             []
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
             (:) v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                []
                  -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
                (:) v3 v4 -> coe d_take'45'coh_464 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad.constT-pf
d_constT'45'pf_500 ::
  () ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_PrefixFamily_396
d_constT'45'pf_500 ~v0 v1 ~v2 = du_constT'45'pf_500 v1
du_constT'45'pf_500 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  T_PrefixFamily_396
du_constT'45'pf_500 v0
  = coe
      C_prefixFamily_414
      (\ v1 -> d_length'45'take'45''8804'_436 (coe v1) (coe v0))
      (\ v1 -> d_take'45'coh_464 (coe v1) (coe v0))
-- Once.Denotation.TraceMonad.tell-pf
d_tell'45'pf_516 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  T_PrefixFamily_396
d_tell'45'pf_516 v0 = coe du_constT'45'pf_500 (coe v0)
-- Once.Denotation.TraceMonad.suc∸
d_suc'8760'_524 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'8760'_524 = erased
-- Once.Denotation.TraceMonad.split-<
d_split'45''60'_538 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_split'45''60'_538 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1))
      (coe v2) (coe v0) (coe v3)
-- Once.Denotation.TraceMonad.pf-retype
d_pf'45'retype_562 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  T_PrefixFamily_396 -> T_PrefixFamily_396
d_pf'45'retype_562 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_pf'45'retype_562 v5
du_pf'45'retype_562 :: T_PrefixFamily_396 -> T_PrefixFamily_396
du_pf'45'retype_562 v0 = coe v0
-- Once.Denotation.TraceMonad.bindRes-pf
d_bindRes'45'pf_584 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
d_bindRes'45'pf_584 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_bindRes'45'pf_584 v2 v3 v4 v5 v6
du_bindRes'45'pf_584 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
du_bindRes'45'pf_584 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v3
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> coe
             C_prefixFamily_414
             (coe du_bnd'8242'_626 (coe v0) (coe v5) (coe v4))
             (coe du_coh'8242'_658 (coe v0) (coe v5) (coe v2) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad._.fy
d_fy_608 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_T_10
d_fy_608 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 = du_fy_608 v3 v4
du_fy_608 :: AgdaAny -> (AgdaAny -> T_T_10) -> T_T_10
du_fy_608 v0 v1 = coe v1 v0
-- Once.Denotation.TraceMonad._.pfy
d_pfy_610 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
d_pfy_610 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_pfy_610 v3 v6
du_pfy_610 ::
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
du_pfy_610 v0 v1 = coe v1 v0 erased
-- Once.Denotation.TraceMonad._.lm
d_lm_612 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> Integer
d_lm_612 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 = du_lm_612 v2 v7
du_lm_612 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  Integer -> Integer
du_lm_612 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_length_268 (coe v0 v1)
-- Once.Denotation.TraceMonad._.rest-of
d_rest'45'of_616 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_rest'45'of_616 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7
  = du_rest'45'of_616 v2 v3 v4 v7
du_rest'45'of_616 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
du_rest'45'of_616 v0 v1 v2 v3
  = coe
      d_trT_18 (coe du_fy_608 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
         (coe du_lm_612 (coe v0) (coe v3)))
-- Once.Denotation.TraceMonad._.len-split
d_len'45'split_622 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_len'45'split_622 = erased
-- Once.Denotation.TraceMonad._.bnd′
d_bnd'8242'_626 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd'8242'_626 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7
  = du_bnd'8242'_626 v2 v3 v6 v7
du_bnd'8242'_626 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd'8242'_626 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
         (coe MAlonzo.Code.Data.List.Base.du_length_268 (coe v0 v3)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe du_lm_612 (coe v0) (coe v3)))
      (coe
         d_bnd_408 (coe du_pfy_610 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
            (coe du_lm_612 (coe v0) (coe v3))))
-- Once.Denotation.TraceMonad._.sat′
d_sat'8242'_634 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat'8242'_634 = erased
-- Once.Denotation.TraceMonad._._.sum<
d_sum'60'_644 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'60'_644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_sum'60'_644 v8
du_sum'60'_644 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sum'60'_644 v0 = coe v0
-- Once.Denotation.TraceMonad._._.lm<k
d_lm'60'k_648 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lm'60'k_648 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_lm'60'k_648 v2 v7 v8
du_lm'60'k_648 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lm'60'k_648 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_lm_612 (coe v0) (coe v1))))
      (coe v2)
-- Once.Denotation.TraceMonad._._.lf<k′
d_lf'60'k'8242'_650 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lf'60'k'8242'_650 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8
  = du_lf'60'k'8242'_650 v2 v3 v4 v7 v8
du_lf'60'k'8242'_650 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lf'60'k'8242'_650 v0 v1 v2 v3 v4
  = coe
      d_split'45''60'_538
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
          coe (coe (\ v6 -> v5)))
         (coe (0 :: Integer)) (coe v0 v3))
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
          coe (coe (\ v6 -> v5)))
         (coe (0 :: Integer))
         (coe
            d_trT_18 (coe v2 v1)
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
               (coe du_lm_612 (coe v0) (coe v3)))))
      (coe v3) (coe v4)
-- Once.Denotation.TraceMonad._._.satm
d_satm_652 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_satm_652 = erased
-- Once.Denotation.TraceMonad._._.restEq
d_restEq_654 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restEq_654 = erased
-- Once.Denotation.TraceMonad._.coh′
d_coh'8242'_658 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh'8242'_658 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_coh'8242'_658 v2 v3 v4 v5 v6 v7
du_coh'8242'_658 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coh'8242'_658 v0 v1 v2 v3 v4 v5
  = coe
      du_go_740 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_m'8804'n'8658'm'60'n'8744'm'8801'n_3260
         (coe
            MAlonzo.Code.Data.List.Base.du_foldr_216
            (let v6 = \ v6 -> addInt (coe (1 :: Integer)) (coe v6) in
             coe (coe (\ v7 -> v6)))
            (coe (0 :: Integer)) (coe v0 v5))
         (coe v5) (coe d_bnd_408 v3 v5))
-- Once.Denotation.TraceMonad._._.spare
d_spare_668 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spare_668 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 ~v8
  = du_spare_668 v2 v3 v6 v7
du_spare_668 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spare_668 v0 v1 v2 v3
  = coe
      d_coh_412 (coe v2 v1 erased)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
         (coe du_lm_612 (coe v0) (coe v3)))
-- Once.Denotation.TraceMonad._._.spent
d_spent_686 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spent_686 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_spent_686 v2 v3 v4 v5 v7
du_spent_686 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spent_686 v0 v1 v2 v3 v4
  = let v5 = coe d_coh_412 v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
                   (coe du_tailPart_704 (coe v0) (coe v1) (coe v4) (coe v2)))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad._._._.tailPart
d_tailPart_704 ::
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  T_PrefixFamily_396 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_tailPart_704 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_tailPart_704 v1 v2 v4 v8
du_tailPart_704 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  Integer ->
  (AgdaAny -> T_T_10) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
du_tailPart_704 v0 v1 v2 v3
  = coe
      du_rest'45'of_616 (coe v0) (coe v1) (coe v3)
      (coe addInt (coe (1 :: Integer)) (coe v2))
-- Once.Denotation.TraceMonad._._._.empty-at-0
d_empty'45'at'45'0_706 ::
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  T_PrefixFamily_396 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_empty'45'at'45'0_706 = erased
-- Once.Denotation.TraceMonad._._._._.len0
d_len0_716 ::
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  T_PrefixFamily_396 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_len0_716 = erased
-- Once.Denotation.TraceMonad._._._.nil-rest
d_nil'45'rest_730 ::
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  T_PrefixFamily_396 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nil'45'rest_730 = erased
-- Once.Denotation.TraceMonad._._.go
d_go_740 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_740 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_go_740 v2 v3 v4 v5 v6 v7 v8
du_go_740 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_740 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe du_spare_668 (coe v0) (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe du_spent_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.>>=T-pf
d_'62''62''61'T'45'pf_756 ::
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
d_'62''62''61'T'45'pf_756 ~v0 ~v1 v2 v3 v4 v5
  = du_'62''62''61'T'45'pf_756 v2 v3 v4 v5
du_'62''62''61'T'45'pf_756 ::
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  T_PrefixFamily_396 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   T_PrefixFamily_396) ->
  T_PrefixFamily_396
du_'62''62''61'T'45'pf_756 v0 v1 v2 v3
  = coe
      du_bindRes'45'pf_584 (coe d_trT_18 (coe v0))
      (coe d_resT_20 (coe v0)) (coe v1) (coe v2) (coe v3)
-- Once.Denotation.TraceMonad.RelRes
d_RelRes_772 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_RelRes_772 = erased
-- Once.Denotation.TraceMonad.RelRes-value
d_RelRes'45'value_790 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_RelRes'45'value_790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_RelRes'45'value_790 v7
du_RelRes'45'value_790 ::
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 -> AgdaAny
du_RelRes'45'value_790 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_rel'45'returns_140 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.RelT′
d_RelT'8242'_800 ::
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> T_T_10 -> T_T_10 -> ()
d_RelT'8242'_800 = erased
-- Once.Denotation.TraceMonad.RelRes-bind
d_RelRes'45'bind_842 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RelRes'45'bind_842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11
                     v12 v13 ~v14
  = du_RelRes'45'bind_842 v6 v8 v9 v12 v13
du_RelRes'45'bind_842 ::
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_RelRes'45'bind_842 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             seq (coe v2)
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4 v3)
                     (coe MAlonzo.Code.Once.Res.C_rel'45'stopped_134)))
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Res.C_returns_12 v6
               -> coe
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               v7 v5 v6 erased erased
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
                                  (coe MAlonzo.Code.Data.List.Base.du_length_268 (coe v0 v3))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.RelT′-bind
d_RelT'8242''45'bind_946 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_T_10 ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RelT'8242''45'bind_946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                         v11 v12
  = du_RelT'8242''45'bind_946 v6 v7 v11 v12
du_RelT'8242''45'bind_946 ::
  T_T_10 ->
  T_T_10 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_RelT'8242''45'bind_946 v0 v1 v2 v3
  = coe
      du_RelRes'45'bind_842 (d_trT_18 (coe v0)) (d_resT_20 (coe v0))
      (d_resT_20 (coe v1)) v3 erased v2
-- Once.Denotation.TraceMonad.>>=T-identityˡ
d_'62''62''61'T'45'identity'737'_978 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'737'_978 = erased
-- Once.Denotation.TraceMonad.>>=T-identityʳ
d_'62''62''61'T'45'identity'691'_992 ::
  () ->
  T_T_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'691'_992 = erased
-- Once.Denotation.TraceMonad.bindRes-idʳ
d_bindRes'45'id'691'_1002 ::
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'id'691'_1002 = erased
-- Once.Denotation.TraceMonad.bindRes-mapʳ
d_bindRes'45'map'691'_1034 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'map'691'_1034 = erased
-- Once.Denotation.TraceMonad.bindRes-rel
d_bindRes'45'rel_1080 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bindRes'45'rel_1080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                      v11 v12 v13
  = du_bindRes'45'rel_1080 v6 v7 v11 v12 v13
du_bindRes'45'rel_1080 ::
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bindRes'45'rel_1080 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe MAlonzo.Code.Once.Res.C_rel'45'stopped_134))
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Res.C_returns_12 v6
               -> case coe v3 of
                    MAlonzo.Code.Once.Res.C_rel'45'returns_140 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe v4 v5 v6 v9 (0 :: Integer)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.bindRes-trʳ
d_bindRes'45'tr'691'_1178 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'tr'691'_1178 = erased
-- Once.Denotation.TraceMonad.>>=T-mapʳ
d_'62''62''61'T'45'map'691'_1206 ::
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'map'691'_1206 = erased
-- Once.Denotation.TraceMonad.>>=T-assoc
d_'62''62''61'T'45'assoc_1230 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'assoc_1230 = erased
-- Once.Denotation.TraceMonad._.go
d_go_1248 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1248 = erased
-- Once.Denotation.TraceMonad._._.es-m
d_es'45'm_1256 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_es'45'm_1256 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 = du_es'45'm_1256 v3
du_es'45'm_1256 ::
  T_T_10 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
du_es'45'm_1256 v0 = coe d_trT_18 (coe v0)
-- Once.Denotation.TraceMonad._._.fy
d_fy_1258 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) -> Integer -> AgdaAny -> T_T_10
d_fy_1258 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 = du_fy_1258 v4 v7
du_fy_1258 :: (AgdaAny -> T_T_10) -> AgdaAny -> T_T_10
du_fy_1258 v0 v1 = coe v0 v1
-- Once.Denotation.TraceMonad._._.inner
d_inner_1266 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_1266 = erased
-- Once.Denotation.TraceMonad._._._.budget
d_budget_1274 ::
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_budget_1274 = erased
-- Once.Denotation.TraceMonad.>>=T-map
d_'62''62''61'T'45'map_1294 ::
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'map_1294 = erased
-- Once.Denotation.TraceMonad.bindRes-map
d_bindRes'45'map_1310 ::
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'map_1310 = erased
-- Once.Denotation.TraceMonad.fmapT->>=T
d_fmapT'45''62''62''61'T_1350 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45''62''62''61'T_1350 = erased
-- Once.Denotation.TraceMonad.bindRes-map-fusion
d_bindRes'45'map'45'fusion_1370 ::
  () ->
  () ->
  () ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindRes'45'map'45'fusion_1370 = erased
-- Once.Denotation.TraceMonad.T-rawFunctor
d_T'45'rawFunctor_1398 ::
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_T'45'rawFunctor_1398
  = coe
      MAlonzo.Code.Effect.Functor.C_constructor_44
      (\ v0 v1 v2 v3 -> coe du_fmapT_92 v2 v3)
-- Once.Denotation.TraceMonad.T-rawApplicative
d_T'45'rawApplicative_1400 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_T'45'rawApplicative_1400
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_78
      (coe d_T'45'rawFunctor_1398) (\ v0 v1 -> coe du_returnT_34 v1)
      (coe
         (\ v0 v1 v2 v3 ->
            coe
              du__'62''62''61'T__70 (coe v2)
              (coe
                 (\ v4 ->
                    coe
                      du__'62''62''61'T__70 (coe v3)
                      (coe (\ v5 -> coe du_returnT_34 (coe v4 v5)))))))
-- Once.Denotation.TraceMonad.T-rawMonad
d_T'45'rawMonad_1410 :: MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_T'45'rawMonad_1410
  = coe
      MAlonzo.Code.Effect.Monad.C_constructor_98
      (coe d_T'45'rawApplicative_1400)
      (\ v0 v1 v2 v3 -> coe du__'62''62''61'T__70 v2 v3)
-- Once.Denotation.TraceMonad._._._>>=_
d__'62''62''61'__1418 ::
  () -> () -> T_T_10 -> (AgdaAny -> T_T_10) -> T_T_10
d__'62''62''61'__1418 v0 v1 v2 v3 = coe du__'62''62''61'T__70 v2 v3
-- Once.Denotation.TraceMonad._._.pure
d_pure_1420 :: () -> AgdaAny -> T_T_10
d_pure_1420 v0 v1 = coe du_returnT_34 v1
-- Once.Denotation.TraceMonad._.IsMonadT
d_IsMonadT_1422 = ()
data T_IsMonadT_1422 = C_constructor_1500
-- Once.Denotation.TraceMonad._.IsMonadT.identityˡ
d_identity'737'_1472 ::
  T_IsMonadT_1422 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1472 = erased
-- Once.Denotation.TraceMonad._.IsMonadT.identityʳ
d_identity'691'_1480 ::
  T_IsMonadT_1422 ->
  () ->
  T_T_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1480 = erased
-- Once.Denotation.TraceMonad._.IsMonadT.assoc
d_assoc_1498 ::
  T_IsMonadT_1422 ->
  () ->
  () ->
  () ->
  T_T_10 ->
  (AgdaAny -> T_T_10) ->
  (AgdaAny -> T_T_10) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1498 = erased
-- Once.Denotation.TraceMonad._.T-isMonad
d_T'45'isMonad_1502 :: T_IsMonadT_1422
d_T'45'isMonad_1502 = erased
-- Once.Denotation.TraceMonad.take-++-split
d_take'45''43''43''45'split_1512 ::
  () ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45''43''43''45'split_1512 = erased
-- Once.Denotation.TraceMonad.minus-take
d_minus'45'take_1540 ::
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_minus'45'take_1540 = erased
-- Once.Denotation.TraceMonad.take-++-threaded
d_take'45''43''43''45'threaded_1560 ::
  () ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45''43''43''45'threaded_1560 = erased
