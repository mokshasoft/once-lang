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

module MAlonzo.Code.Data.Nat.Show.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Show

-- Data.Nat.Show.Properties._.charsInBase-base
d_charsInBase'45'base_18 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_charsInBase'45'base_18 v0 ~v1 ~v2 = du_charsInBase'45'base_18 v0
du_charsInBase'45'base_18 ::
  Integer -> Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_charsInBase'45'base_18 v0
  = coe MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe v0)
-- Data.Nat.Show.Properties._.toDigits-injective-base
d_toDigits'45'injective'45'base_20 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toDigits'45'injective'45'base_20 = erased
-- Data.Nat.Show.Properties._.showDigit-injective-base
d_showDigit'45'injective'45'base_22 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_showDigit'45'injective'45'base_22 = erased
-- Data.Nat.Show.Properties._.charsInBase-injective
d_charsInBase'45'injective_28 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_charsInBase'45'injective_28 = erased
