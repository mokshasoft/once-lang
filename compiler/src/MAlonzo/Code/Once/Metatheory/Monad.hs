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

module MAlonzo.Code.Once.Metatheory.Monad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Once.Denotation.TraceMonad

-- Once.Metatheory.Monad.LawfulMonad
d_LawfulMonad_8 a0 = ()
data T_LawfulMonad_8
  = C_constructor_98 (() -> AgdaAny -> AgdaAny)
                     (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Once.Metatheory.Monad.LawfulMonad.return
d_return_56 :: T_LawfulMonad_8 -> () -> AgdaAny -> AgdaAny
d_return_56 v0
  = case coe v0 of
      C_constructor_98 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Monad.LawfulMonad._>>=_
d__'62''62''61'__62 ::
  T_LawfulMonad_8 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__62 v0
  = case coe v0 of
      C_constructor_98 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Metatheory.Monad.LawfulMonad.identityˡ
d_identity'737'_72 ::
  T_LawfulMonad_8 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_72 = erased
-- Once.Metatheory.Monad.LawfulMonad.identityʳ
d_identity'691'_78 ::
  T_LawfulMonad_8 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_78 = erased
-- Once.Metatheory.Monad.LawfulMonad.assoc
d_assoc_94 ::
  T_LawfulMonad_8 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_94 = erased
-- Once.Metatheory.Monad.LawfulMonad.rawMonad
d_rawMonad_96 ::
  (() -> ()) ->
  T_LawfulMonad_8 -> MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_rawMonad_96 ~v0 v1 = du_rawMonad_96 v1
du_rawMonad_96 ::
  T_LawfulMonad_8 -> MAlonzo.Code.Effect.Monad.T_RawMonad_24
du_rawMonad_96 v0
  = coe
      MAlonzo.Code.Effect.Monad.du_mkRawMonad_180
      (coe d_return_56 (coe v0)) (coe d__'62''62''61'__62 (coe v0))
-- Once.Metatheory.Monad.T-monad
d_T'45'monad_100 :: T_LawfulMonad_8
d_T'45'monad_100
  = coe
      C_constructor_98
      (\ v0 ->
         coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194)
      (\ v0 v1 v2 v3 ->
         coe
           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200 v2
           v3)
