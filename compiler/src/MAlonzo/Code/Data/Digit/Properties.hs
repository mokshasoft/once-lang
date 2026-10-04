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

module MAlonzo.Code.Data.Digit.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Digit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs
import qualified MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Digit.Properties.digitCharsUnique
d_digitCharsUnique_6 ::
  MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.Core.T_AllPairs_22
d_digitCharsUnique_6
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_from'45'yes_168
      (coe
         MAlonzo.Code.Data.Vec.Relation.Unary.AllPairs.du_allPairs'63'_122
         (coe
            (\ v0 v1 ->
               coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                 (coe
                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                    (coe v1))))
         (coe MAlonzo.Code.Data.Digit.d_digitChars_192))
-- Data.Digit.Properties._._.toDigits-injective
d_toDigits'45'injective_30 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toDigits'45'injective_30 = erased
-- Data.Digit.Properties._._.showDigit-injective
d_showDigit'45'injective_54 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_showDigit'45'injective_54 = erased
