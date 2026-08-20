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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
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
               v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v2)) v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v2)) v2))
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
d_tell_56 v0 ~v1 = du_tell_56 v0
du_tell_56 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tell_56 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.TraceMonad.projTrace
d_projTrace_62 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_projTrace_62 ~v0 v1 v2 = du_projTrace_62 v1 v2
du_projTrace_62 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_projTrace_62 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 v1)
-- Once.Denotation.TraceMonad.valueT
d_valueT_70 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny
d_valueT_70 ~v0 v1 v2 = du_valueT_70 v1 v2
du_valueT_70 ::
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny
du_valueT_70 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 v1)
