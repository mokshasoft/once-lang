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

module MAlonzo.Code.Once.Parser.CharClass where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Parser.CharClass.isLowerWord
d_isLowerWord_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isLowerWord_6 v0
  = let v1
          = coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 in
    coe
      (case coe v1 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         (:) v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
