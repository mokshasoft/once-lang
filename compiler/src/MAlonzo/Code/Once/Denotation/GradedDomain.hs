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

module MAlonzo.Code.Once.Denotation.GradedDomain where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Denotation.GradedDomain.M
d_M_6 :: MAlonzo.Code.Once.Type.T_Purity_32 -> () -> ()
d_M_6 = erased
-- Once.Denotation.GradedDomain._>>=ᵖ_
d__'62''62''61''7510'__16 ::
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61''7510'__16 ~v0 ~v1 v2 v3
  = du__'62''62''61''7510'__16 v2 v3
du__'62''62''61''7510'__16 ::
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61''7510'__16 v0 v1 = coe v1 v0
-- Once.Denotation.GradedDomain.>>=ᵖ-β
d_'62''62''61''7510''45'β_30 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'β_30 = erased
-- Once.Denotation.GradedDomain.>>=ᵖ-assoc
d_'62''62''61''7510''45'assoc_50 ::
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'assoc_50 = erased
-- Once.Denotation.GradedDomain.>>=ᵖ-idʳ
d_'62''62''61''7510''45'id'691'_64 ::
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''7510''45'id'691'_64 = erased
-- Once.Denotation.GradedDomain.bindM
d_bindM_74 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bindM_74 v0 ~v1 ~v2 v3 v4 = du_bindM_74 v0 v3 v4
du_bindM_74 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bindM_74 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe du__'62''62''61''7510'__16 (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedDomain.subM
d_subM_90 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  () -> AgdaAny -> AgdaAny
d_subM_90 ~v0 ~v1 v2 ~v3 v4 = du_subM_90 v2 v4
du_subM_90 ::
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 -> AgdaAny -> AgdaAny
du_subM_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'pure_8 -> coe v1
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'eff_10 -> coe v1
      MAlonzo.Code.Once.Type.Sub.C_'8849''45'pe_12
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedDomain.returnM
d_returnM_102 ::
  MAlonzo.Code.Once.Type.T_Purity_32 -> () -> AgdaAny -> AgdaAny
d_returnM_102 v0 ~v1 v2 = du_returnM_102 v0 v2
du_returnM_102 ::
  MAlonzo.Code.Once.Type.T_Purity_32 -> AgdaAny -> AgdaAny
du_returnM_102 v0 v1
  = coe
      du_subM_90
      (coe MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0)) (coe v1)
-- Once.Denotation.GradedDomain.bindM-idˡ
d_bindM'45'id'737'_118 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindM'45'id'737'_118 = erased
-- Once.Denotation.GradedDomain.toT
d_toT_132 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_toT_132 v0 ~v1 v2 = du_toT_132 v0 v2
du_toT_132 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_toT_132 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v1
      MAlonzo.Code.Once.Type.C_eff_36 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedDomain.νᵖ
d_ν'7510'_140 a0 = ()
data T_ν'7510'_140 = C_constructor_148 AgdaAny
-- Once.Denotation.GradedDomain.νᵖ.forceᵖ
d_force'7510'_146 :: T_ν'7510'_140 -> AgdaAny
d_force'7510'_146 v0
  = case coe v0 of
      C_constructor_148 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedDomain.⟦_⟧ᵛ
d_'10214'_'10215''7515'_150 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7515'_150 = erased
