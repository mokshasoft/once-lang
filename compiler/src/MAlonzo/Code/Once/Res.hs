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

module MAlonzo.Code.Once.Res where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- Once.Res.Res
d_Res_6 a0 = ()
data T_Res_6 = C_stopped_10 | C_returns_12 AgdaAny
-- Once.Res.is-stopped
d_is'45'stopped_16 :: () -> T_Res_6 -> Bool
d_is'45'stopped_16 ~v0 v1 = du_is'45'stopped_16 v1
du_is'45'stopped_16 :: T_Res_6 -> Bool
du_is'45'stopped_16 v0
  = case coe v0 of
      C_stopped_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_returns_12 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Res.res-returns
d_res'45'returns_24 ::
  () ->
  T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_res'45'returns_24 ~v0 v1 ~v2 = du_res'45'returns_24 v1
du_res'45'returns_24 ::
  T_Res_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_res'45'returns_24 v0
  = case coe v0 of
      C_returns_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Res.res-stopped
d_res'45'stopped_32 ::
  () ->
  T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'stopped_32 = erased
-- Once.Res.returns-inj
d_returns'45'inj_40 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_returns'45'inj_40 = erased
-- Once.Res.mapRes
d_mapRes_46 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_Res_6 -> T_Res_6
d_mapRes_46 ~v0 ~v1 v2 v3 = du_mapRes_46 v2 v3
du_mapRes_46 :: (AgdaAny -> AgdaAny) -> T_Res_6 -> T_Res_6
du_mapRes_46 v0 v1
  = case coe v1 of
      C_stopped_10 -> coe v1
      C_returns_12 v2 -> coe C_returns_12 (coe v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Res.mapRes-id
d_mapRes'45'id_60 ::
  () -> T_Res_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapRes'45'id_60 = erased
-- Once.Res.mapRes-∘
d_mapRes'45''8728'_76 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_Res_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapRes'45''8728'_76 = erased
-- Once.Res.mapRes-cong
d_mapRes'45'cong_98 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Res_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapRes'45'cong_98 = erased
-- Once.Res.is-stopped-mapRes
d_is'45'stopped'45'mapRes_114 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Res_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_is'45'stopped'45'mapRes_114 = erased
-- Once.Res.Res-rel
d_Res'45'rel_126 a0 a1 a2 a3 a4 = ()
data T_Res'45'rel_126
  = C_rel'45'stopped_134 | C_rel'45'returns_140 AgdaAny
-- Once.Res.returns≢stopped
d_returns'8802'stopped_148 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> () -> AgdaAny
d_returns'8802'stopped_148 ~v0 ~v1 ~v2 ~v3
  = du_returns'8802'stopped_148
du_returns'8802'stopped_148 :: AgdaAny
du_returns'8802'stopped_148 = MAlonzo.RTE.mazUnreachableError
