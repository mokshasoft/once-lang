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

module MAlonzo.Code.Once.Denotation.Behavior where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Denotation.Trace

-- Once.Denotation.Behavior.Behavior
d_Behavior_6 = ()
data T_Behavior_6
  = C_mkBehavior_40 (Integer ->
                     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124])
                    (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                    (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.Denotation.Behavior.Behavior.at
d_at_24 ::
  T_Behavior_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_at_24 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.extends
d_extends_30 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extends_30 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.bounded
d_bounded_34 ::
  T_Behavior_6 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bounded_34 v0
  = case coe v0 of
      C_mkBehavior_40 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Behavior.saturates
d_saturates_38 ::
  T_Behavior_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_saturates_38 = erased
-- Once.Denotation.Behavior.silent
d_silent_42 :: T_Behavior_6
d_silent_42
  = coe
      C_mkBehavior_40
      (\ v0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased)
      (\ v0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Denotation.Behavior.Source
d_Source_44 = ()
data T_Source_44
  = C_mkSource_54 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                  MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Denotation.Behavior.Source.srcImports
d_srcImports_50 ::
  T_Source_44 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_srcImports_50 v0
  = case coe v0 of
      C_mkSource_54 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Source.srcText
d_srcText_52 ::
  T_Source_44 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_srcText_52 v0
  = case coe v0 of
      C_mkSource_54 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
