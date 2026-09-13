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

-- Once.Denotation.TraceMonad.T
d_T_6 :: () -> ()
d_T_6 = erased
-- Once.Denotation.TraceMonad.returnT
d_returnT_12 ::
  () -> AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_returnT_12 ~v0 v1 ~v2 = du_returnT_12 v1
du_returnT_12 :: AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_returnT_12 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0)
-- Once.Denotation.TraceMonad._>>=T_
d__'62''62''61'T__20 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61'T__20 ~v0 ~v1 v2 v3 v4
  = du__'62''62''61'T__20 v2 v3 v4
du__'62''62''61'T__20 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62''61'T__20 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v2))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                  (coe
                     MAlonzo.Code.Data.List.Base.du_length_268
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v2)))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v2))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
               (coe
                  MAlonzo.Code.Data.List.Base.du_length_268
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v2))))))
-- Once.Denotation.TraceMonad._>>T_
d__'62''62'T__36 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62'T__36 ~v0 ~v1 v2 v3 = du__'62''62'T__36 v2 v3
du__'62''62'T__36 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62'T__36 v0 v1
  = coe du__'62''62''61'T__20 (coe v0) (coe (\ v2 -> v1))
-- Once.Denotation.TraceMonad.fmapT
d_fmapT_48 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fmapT_48 ~v0 ~v1 v2 v3 v4 = du_fmapT_48 v2 v3 v4
du_fmapT_48 ::
  (AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fmapT_48 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v2))
      (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1 v2)))
-- Once.Denotation.TraceMonad.tell
d_tell_56 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tell_56 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.List.Base.du_take_530 (coe v1) (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.TraceMonad.projTrace
d_projTrace_64 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_projTrace_64 ~v0 v1 v2 = du_projTrace_64 v1 v2
du_projTrace_64 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_projTrace_64 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1)
-- Once.Denotation.TraceMonad.valueT
d_valueT_72 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny
d_valueT_72 ~v0 v1 v2 = du_valueT_72 v1 v2
du_valueT_72 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny
du_valueT_72 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1)
-- Once.Denotation.TraceMonad.bindAt
d_bindAt_82 ::
  () ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bindAt_82 ~v0 ~v1 v2 v3 v4 = du_bindAt_82 v2 v3 v4
du_bindAt_82 ::
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bindAt_82 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                  (coe
                     MAlonzo.Code.Data.List.Base.du_length_268
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
               (coe
                  MAlonzo.Code.Data.List.Base.du_length_268
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))))))
-- Once.Denotation.TraceMonad.>>=T-at
d_'62''62''61'T'45'at_102 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'at_102 = erased
-- Once.Denotation.TraceMonad.>>=T-cong-at
d_'62''62''61'T'45'cong'45'at_122 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'cong'45'at_122 = erased
-- Once.Denotation.TraceMonad.bindAt-cong
d_bindAt'45'cong_148 ::
  () ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindAt'45'cong_148 = erased
-- Once.Denotation.TraceMonad.>>=T-cong₂-at
d_'62''62''61'T'45'cong'8322''45'at_180 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'cong'8322''45'at_180 = erased
-- Once.Denotation.TraceMonad.Bounded
d_Bounded_194 ::
  () -> (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_Bounded_194 = erased
-- Once.Denotation.TraceMonad.Saturating
d_Saturating_202 ::
  () -> (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_Saturating_202 = erased
-- Once.Denotation.TraceMonad.Coherent
d_Coherent_210 ::
  () -> (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_Coherent_210 = erased
-- Once.Denotation.TraceMonad.PrefixFamily
d_PrefixFamily_222 a0 a1 = ()
data T_PrefixFamily_222
  = C_prefixFamily_240 (Integer ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Denotation.TraceMonad.PrefixFamily.bnd
d_bnd_234 ::
  T_PrefixFamily_222 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_234 v0
  = case coe v0 of
      C_prefixFamily_240 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.PrefixFamily.sat
d_sat_236 ::
  T_PrefixFamily_222 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_236 = erased
-- Once.Denotation.TraceMonad.PrefixFamily.coh
d_coh_238 ::
  T_PrefixFamily_222 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh_238 v0
  = case coe v0 of
      C_prefixFamily_240 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.returnT-pf
d_returnT'45'pf_246 :: () -> AgdaAny -> T_PrefixFamily_222
d_returnT'45'pf_246 ~v0 ~v1 = du_returnT'45'pf_246
du_returnT'45'pf_246 :: T_PrefixFamily_222
du_returnT'45'pf_246
  = coe
      C_prefixFamily_240
      (\ v0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased)
-- Once.Denotation.TraceMonad.length-take-≤
d_length'45'take'45''8804'_262 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'take'45''8804'_262 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (d_length'45'take'45''8804'_262 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad.take-sat
d_take'45'sat_272 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'sat_272 = erased
-- Once.Denotation.TraceMonad.take-coh
d_take'45'coh_290 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_take'45'coh_290 v0 v1
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
                (:) v3 v4 -> coe d_take'45'coh_290 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad.constT-pf
d_constT'45'pf_326 ::
  () ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  AgdaAny -> T_PrefixFamily_222
d_constT'45'pf_326 ~v0 v1 ~v2 = du_constT'45'pf_326 v1
du_constT'45'pf_326 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  T_PrefixFamily_222
du_constT'45'pf_326 v0
  = coe
      C_prefixFamily_240
      (\ v1 -> d_length'45'take'45''8804'_262 (coe v1) (coe v0))
      (\ v1 -> d_take'45'coh_290 (coe v1) (coe v0))
-- Once.Denotation.TraceMonad.tell-pf
d_tell'45'pf_344 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  T_PrefixFamily_222
d_tell'45'pf_344 v0 = coe du_constT'45'pf_326 (coe v0)
-- Once.Denotation.TraceMonad.suc∸
d_suc'8760'_352 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'8760'_352 = erased
-- Once.Denotation.TraceMonad.split-<
d_split'45''60'_366 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_split'45''60'_366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'737''45''8804'_5232
      (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1))
      (coe v2) (coe v0) (coe v3)
-- Once.Denotation.TraceMonad.>>=T-pf
d_'62''62''61'T'45'pf_390 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) -> T_PrefixFamily_222
d_'62''62''61'T'45'pf_390 ~v0 ~v1 v2 v3 v4 v5
  = du_'62''62''61'T'45'pf_390 v2 v3 v4 v5
du_'62''62''61'T'45'pf_390 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) -> T_PrefixFamily_222
du_'62''62''61'T'45'pf_390 v0 v1 v2 v3
  = coe
      C_prefixFamily_240 (coe du_bnd'8242'_422 (coe v0) (coe v3))
      (coe du_coh'8242'_460 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Denotation.TraceMonad._.lm
d_lm_404 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) -> Integer -> Integer
d_lm_404 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 = du_lm_404 v2 v6
du_lm_404 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
du_lm_404 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe du_projTrace_64 (coe v0) (coe v1))
-- Once.Denotation.TraceMonad._.xv
d_xv_408 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) -> Integer -> AgdaAny
d_xv_408 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 = du_xv_408 v2 v6
du_xv_408 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny
du_xv_408 v0 v1 = coe du_valueT_72 (coe v0) (coe v1)
-- Once.Denotation.TraceMonad._.rest-of
d_rest'45'of_412 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_rest'45'of_412 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_rest'45'of_412 v2 v3 v6
du_rest'45'of_412 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_rest'45'of_412 v0 v1 v2
  = coe
      du_projTrace_64 (coe v1 (coe du_xv_408 (coe v0) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
         (coe du_lm_404 (coe v0) (coe v2)))
-- Once.Denotation.TraceMonad._.len-split
d_len'45'split_418 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_len'45'split_418 = erased
-- Once.Denotation.TraceMonad._.bnd′
d_bnd'8242'_422 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd'8242'_422 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_bnd'8242'_422 v2 v5 v6
du_bnd'8242'_422 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bnd'8242'_422 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3672
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe du_projTrace_64 (coe v0) (coe v2))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe du_lm_404 (coe v0) (coe v2)))
      (coe
         d_bnd_234 (coe v1 v2)
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
            (coe du_lm_404 (coe v0) (coe v2))))
-- Once.Denotation.TraceMonad._.sat′
d_sat'8242'_430 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat'8242'_430 = erased
-- Once.Denotation.TraceMonad._._.sum<
d_sum'60'_440 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'60'_440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sum'60'_440 v7
du_sum'60'_440 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sum'60'_440 v0 = coe v0
-- Once.Denotation.TraceMonad._._.lm<k
d_lm'60'k_444 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lm'60'k_444 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_lm'60'k_444 v2 v6 v7
du_lm'60'k_444 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lm'60'k_444 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe du_lm_404 (coe v0) (coe v1))))
      (coe v2)
-- Once.Denotation.TraceMonad._._.lf<k'
d_lf'60'k''_446 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lf'60'k''_446 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7
  = du_lf'60'k''_446 v2 v3 v6 v7
du_lf'60'k''_446 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lf'60'k''_446 v0 v1 v2 v3
  = coe
      d_split'45''60'_366
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (let v4 = \ v4 -> addInt (coe (1 :: Integer)) (coe v4) in
          coe (coe (\ v5 -> v4)))
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v2)))
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (let v4 = \ v4 -> addInt (coe (1 :: Integer)) (coe v4) in
          coe (coe (\ v5 -> v4)))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               v1 (coe du_xv_408 (coe v0) (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                  (coe du_lm_404 (coe v0) (coe v2))))))
      (coe v2) (coe v3)
-- Once.Denotation.TraceMonad._._.seq
d_seq_448 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seq_448 = erased
-- Once.Denotation.TraceMonad._.coh′
d_coh'8242'_460 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh'8242'_460 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_coh'8242'_460 v2 v3 v4 v5 v6
du_coh'8242'_460 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coh'8242'_460 v0 v1 v2 v3 v4
  = coe
      du_go_550 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_m'8804'n'8658'm'60'n'8744'm'8801'n_3260
         (coe
            MAlonzo.Code.Data.List.Base.du_foldr_216
            (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
             coe (coe (\ v6 -> v5)))
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v4)))
         (coe v4) (coe d_bnd_234 v2 v4))
-- Once.Denotation.TraceMonad._._.spare
d_spare_470 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spare_470 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 = du_spare_470 v2 v5 v6
du_spare_470 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spare_470 v0 v1 v2
  = coe
      d_coh_238 (coe v1 v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
         (coe du_lm_404 (coe v0) (coe v2)))
-- Once.Denotation.TraceMonad._._.spent
d_spent_492 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spent_492 ~v0 ~v1 v2 v3 v4 ~v5 v6 ~v7 = du_spent_492 v2 v3 v4 v6
du_spent_492 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spent_492 v0 v1 v2 v3
  = let v4 = coe d_coh_238 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                   (coe du_tailPart_510 (coe v0) (coe v3) (coe v1)))
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonad._._._.tailPart
d_tailPart_510 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_tailPart_510 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_tailPart_510 v1 v3 v7
du_tailPart_510 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_tailPart_510 v0 v1 v2
  = coe
      du_rest'45'of_412 (coe v0) (coe v2)
      (coe addInt (coe (1 :: Integer)) (coe v1))
-- Once.Denotation.TraceMonad._._._.nil-rest
d_nil'45'rest_512 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nil'45'rest_512 = erased
-- Once.Denotation.TraceMonad._._._._.empty-at-0
d_empty'45'at'45'0_518 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_empty'45'at'45'0_518 = erased
-- Once.Denotation.TraceMonad._._._._._.len0
d_len0_528 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> T_PrefixFamily_222) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_len0_528 = erased
-- Once.Denotation.TraceMonad._._.go
d_go_550 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_550 ~v0 ~v1 v2 v3 v4 v5 v6 v7 = du_go_550 v2 v3 v4 v5 v6 v7
du_go_550 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_PrefixFamily_222 ->
  (Integer -> T_PrefixFamily_222) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_550 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe du_spare_470 (coe v0) (coe v3) (coe v4)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe du_spent_492 (coe v0) (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonad.RelT′
d_RelT'8242'_562 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelT'8242'_562 = erased
-- Once.Denotation.TraceMonad.RelT′-bind
d_RelT'8242''45'bind_594 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RelT'8242''45'bind_594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
                         ~v10 v11 v12
  = du_RelT'8242''45'bind_594 v6 v11 v12
du_RelT'8242''45'bind_594 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_RelT'8242''45'bind_594 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe v1 v2 (coe du_kL_618 (coe v0) (coe v2))))
-- Once.Denotation.TraceMonad._.kL
d_kL_618 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
d_kL_618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_kL_618 v6 v12
du_kL_618 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
du_kL_618 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268
         (coe du_projTrace_64 (coe v0) (coe v1)))
-- Once.Denotation.TraceMonad._.keq
d_keq_620 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keq_620 = erased
-- Once.Denotation.TraceMonad.>>=T-identityˡ
d_'62''62''61'T'45'identity'737'_638 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'737'_638 = erased
-- Once.Denotation.TraceMonad.>>=T-identityʳ
d_'62''62''61'T'45'identity'691'_652 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'identity'691'_652 = erased
-- Once.Denotation.TraceMonad.>>=T-assoc
d_'62''62''61'T'45'assoc_674 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'assoc_674 = erased
-- Once.Denotation.TraceMonad._.es-m
d_es'45'm_688 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_es'45'm_688 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_es'45'm_688 v3 v6
du_es'45'm_688 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_es'45'm_688 v0 v1 = coe du_projTrace_64 (coe v0) (coe v1)
-- Once.Denotation.TraceMonad._.k₁
d_k'8321'_690 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
d_k'8321'_690 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_k'8321'_690 v3 v6
du_k'8321'_690 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
du_k'8321'_690 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268
         (coe du_es'45'm_688 (coe v0) (coe v1)))
-- Once.Denotation.TraceMonad._.es-f
d_es'45'f_692 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_es'45'f_692 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 = du_es'45'f_692 v3 v4 v6
du_es'45'f_692 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_es'45'f_692 v0 v1 v2
  = coe
      du_projTrace_64 (coe v1 (coe du_valueT_72 (coe v0) (coe v2)))
      (coe du_k'8321'_690 (coe v0) (coe v2))
-- Once.Denotation.TraceMonad._.k₂
d_k'8322'_694 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
d_k'8322'_694 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 = du_k'8322'_694 v3 v4 v6
du_k'8322'_694 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> Integer
du_k'8322'_694 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (coe du_k'8321'_690 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268
         (coe du_es'45'f_692 (coe v0) (coe v1) (coe v2)))
-- Once.Denotation.TraceMonad._.budget
d_budget_696 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_budget_696 = erased
-- Once.Denotation.TraceMonad._.tr
d_tr_702 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr_702 = erased
-- Once.Denotation.TraceMonad._.es-g
d_es'45'g_704 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_es'45'g_704 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_es'45'g_704 v3 v4 v5 v6
du_es'45'g_704 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_es'45'g_704 v0 v1 v2 v3
  = coe
      du_projTrace_64
      (coe
         v2
         (coe
            du_valueT_72 (coe v1 (coe du_valueT_72 (coe v0) (coe v3)))
            (coe du_k'8321'_690 (coe v0) (coe v3))))
      (coe du_k'8322'_694 (coe v0) (coe v1) (coe v3))
-- Once.Denotation.TraceMonad._.vl
d_vl_710 ::
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vl_710 = erased
-- Once.Denotation.TraceMonad.>>=T-map
d_'62''62''61'T'45'map_726 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61'T'45'map_726 = erased
-- Once.Denotation.TraceMonad.fmapT->>=T
d_fmapT'45''62''62''61'T_750 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45''62''62''61'T_750 = erased
-- Once.Denotation.TraceMonad.T-rawFunctor
d_T'45'rawFunctor_760 ::
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_T'45'rawFunctor_760
  = coe
      MAlonzo.Code.Effect.Functor.C_constructor_44
      (\ v0 v1 v2 v3 v4 -> coe du_fmapT_48 v2 v3 v4)
-- Once.Denotation.TraceMonad.T-rawApplicative
d_T'45'rawApplicative_762 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_T'45'rawApplicative_762
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_78
      (coe d_T'45'rawFunctor_760) (\ v0 v1 v2 -> coe du_returnT_12 v1)
      (coe
         (\ v0 v1 v2 v3 ->
            coe
              du__'62''62''61'T__20 (coe v2)
              (coe
                 (\ v4 ->
                    coe
                      du__'62''62''61'T__20 (coe v3)
                      (coe (\ v5 v6 -> coe du_returnT_12 (coe v4 v5)))))))
-- Once.Denotation.TraceMonad.T-rawMonad
d_T'45'rawMonad_772 :: MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_T'45'rawMonad_772
  = coe
      MAlonzo.Code.Effect.Monad.C_constructor_98
      (coe d_T'45'rawApplicative_762)
      (\ v0 v1 v2 v3 v4 -> coe du__'62''62''61'T__20 v2 v3 v4)
-- Once.Denotation.TraceMonad._._._>>=_
d__'62''62''61'__780 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61'__780 v0 v1 v2 v3 v4
  = coe du__'62''62''61'T__20 v2 v3 v4
-- Once.Denotation.TraceMonad._._.pure
d_pure_782 ::
  () -> AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pure_782 v0 v1 v2 = coe du_returnT_12 v1
-- Once.Denotation.TraceMonad._.IsMonadT
d_IsMonadT_784 = ()
data T_IsMonadT_784 = C_constructor_862
-- Once.Denotation.TraceMonad._.IsMonadT.identityˡ
d_identity'737'_834 ::
  T_IsMonadT_784 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_834 = erased
-- Once.Denotation.TraceMonad._.IsMonadT.identityʳ
d_identity'691'_842 ::
  T_IsMonadT_784 ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_842 = erased
-- Once.Denotation.TraceMonad._.IsMonadT.assoc
d_assoc_860 ::
  T_IsMonadT_784 ->
  () ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_860 = erased
-- Once.Denotation.TraceMonad._.T-isMonad
d_T'45'isMonad_864 :: T_IsMonadT_784
d_T'45'isMonad_864 = erased
