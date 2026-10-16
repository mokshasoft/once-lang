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

module MAlonzo.Code.Once.Denotation.GradedDomainLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub

-- Once.Denotation.GradedDomainLaws.>>=ᵖ-β
d_'62''62''61''7510''45'β_14 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'β_14 = erased
-- Once.Denotation.GradedDomainLaws.>>=ᵖ-assoc
d_'62''62''61''7510''45'assoc_34 ::
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'assoc_34 = erased
-- Once.Denotation.GradedDomainLaws.>>=ᵖ-idʳ
d_'62''62''61''7510''45'id'691'_48 ::
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'id'691'_48 = erased
-- Once.Denotation.GradedDomainLaws.bindM-idˡ
d_bindM'45'id'737'_64 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bindM'45'id'737'_64 ~v0 v1 ~v2 ~v3 v4 v5
  = du_bindM'45'id'737'_64 v1 v4 v5
du_bindM'45'id'737'_64 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bindM'45'id'737'_64 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'id'737'_396
             (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
