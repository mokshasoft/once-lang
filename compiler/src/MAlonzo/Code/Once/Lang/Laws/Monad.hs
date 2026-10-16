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

module MAlonzo.Code.Once.Lang.Laws.Monad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Once.Lang.Trace

-- Once.Lang.Laws.Monad.LawfulMonad
d_LawfulMonad_10 a0 = ()
data T_LawfulMonad_10
  = C_constructor_100 (() -> AgdaAny -> AgdaAny)
                      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Once.Lang.Laws.Monad.LawfulMonad.return
d_return_58 :: T_LawfulMonad_10 -> () -> AgdaAny -> AgdaAny
d_return_58 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.Monad.LawfulMonad._>>=_
d__'62''62''61'__64 ::
  T_LawfulMonad_10 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__64 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.Monad.LawfulMonad.identityˡ
d_identity'737'_74 ::
  T_LawfulMonad_10 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_74 = erased
-- Once.Lang.Laws.Monad.LawfulMonad.identityʳ
d_identity'691'_80 ::
  T_LawfulMonad_10 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_80 = erased
-- Once.Lang.Laws.Monad.LawfulMonad.assoc
d_assoc_96 ::
  T_LawfulMonad_10 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_96 = erased
-- Once.Lang.Laws.Monad.LawfulMonad.rawMonad
d_rawMonad_98 ::
  (() -> ()) ->
  T_LawfulMonad_10 -> MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_rawMonad_98 ~v0 v1 = du_rawMonad_98 v1
du_rawMonad_98 ::
  T_LawfulMonad_10 -> MAlonzo.Code.Effect.Monad.T_RawMonad_24
du_rawMonad_98 v0
  = coe
      MAlonzo.Code.Effect.Monad.du_mkRawMonad_180
      (coe d_return_58 (coe v0)) (coe d__'62''62''61'__64 (coe v0))
-- Once.Lang.Laws.Monad.T-monad
d_T'45'monad_102 :: T_LawfulMonad_10
d_T'45'monad_102
  = coe
      C_constructor_100
      (\ v0 -> coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126)
      (\ v0 v1 v2 v3 ->
         coe MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 v2 v3)
