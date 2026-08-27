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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.ArithSimPathLoad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Arith.Machine.Shape

-- Once.Adequacy.ArchCorrectness.ArithSimPathLoad.path-load-go
d_path'45'load'45'go_16 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'load'45'go_16 ~v0 v1 v2 v3 v4 v5 v6
  = du_path'45'load'45'go_16 v1 v2 v3 v4 v5 v6
du_path'45'load'45'go_16 ::
  (AgdaAny -> Integer -> Maybe Integer) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer) ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
du_path'45'load'45'go_16 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      [] -> coe v1 (coe v0 v3 v4)
      (:) v6 v7
        -> coe
             du_path'45'load'45'go_16 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v1 (coe v0 v3 (addInt (coe v2 v6) (coe v4)))) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoad.plg-mem-cong
d_plg'45'mem'45'cong_38 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (Maybe Integer -> Integer) ->
  (MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24 -> Integer) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_plg'45'mem'45'cong_38 = erased
