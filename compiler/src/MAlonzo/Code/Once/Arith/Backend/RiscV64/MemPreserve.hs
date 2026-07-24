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

module MAlonzo.Code.Once.Arith.Backend.RiscV64.MemPreserve where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Arith.Backend.RiscV64.MemPreserve.readMem-writeMem-other
d_readMem'45'writeMem'45'other_18 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readMem'45'writeMem'45'other_18 = erased
-- Once.Arith.Backend.RiscV64.MemPreserve._.AgreeMemFrom
d_AgreeMemFrom_58 ::
  Integer ->
  (Integer -> Maybe Integer) -> (Integer -> Maybe Integer) -> ()
d_AgreeMemFrom_58 = erased
-- Once.Arith.Backend.RiscV64.MemPreserve._.AgreeMemFrom-refl
d_AgreeMemFrom'45'refl_60 ::
  Integer ->
  (Integer -> Maybe Integer) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_AgreeMemFrom'45'refl_60 = erased
-- Once.Arith.Backend.RiscV64.MemPreserve._.AgreeMemFrom-trans
d_AgreeMemFrom'45'trans_62 ::
  Integer ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_AgreeMemFrom'45'trans_62 = erased
-- Once.Arith.Backend.RiscV64.MemPreserve._.writeMem-below-preserves
d_writeMem'45'below'45'preserves_64 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeMem'45'below'45'preserves_64 = erased
