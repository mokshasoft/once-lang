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

module MAlonzo.Code.Relation.Binary.PropositionalEquality.TrustMe where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Binary.PropositionalEquality.TrustMe.trustMe
d_trustMe_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trustMe_16 = erased
-- Relation.Binary.PropositionalEquality.TrustMe.erase
d_erase_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase_26 = erased
-- Relation.Binary.PropositionalEquality.TrustMe.postulate[_↦_]
d_postulate'91'_'8614'_'93'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_postulate'91'_'8614'_'93'_40 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_postulate'91'_'8614'_'93'_40 v5
du_postulate'91'_'8614'_'93'_40 :: AgdaAny -> AgdaAny
du_postulate'91'_'8614'_'93'_40 v0 = coe v0
