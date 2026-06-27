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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Denotation.Behavior.Behavior
d_Behavior_6 :: ()
d_Behavior_6 = erased
-- Once.Denotation.Behavior.Source
d_Source_8 = ()
data T_Source_8
  = C_mkSource_18 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                  MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Denotation.Behavior.Source.srcImports
d_srcImports_14 ::
  T_Source_8 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_srcImports_14 v0
  = case coe v0 of
      C_mkSource_18 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Behavior.Source.srcText
d_srcText_16 ::
  T_Source_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_srcText_16 v0
  = case coe v0 of
      C_mkSource_18 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
