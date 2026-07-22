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

module MAlonzo.Code.Once.Arith.Backend.MemPreserveCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base

-- Once.Arith.Backend.MemPreserveCore.AgreeMemFrom
d_AgreeMemFrom_24 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> AgdaAny -> AgdaAny -> ()
d_AgreeMemFrom_24 = erased
-- Once.Arith.Backend.MemPreserveCore.AgreeMemFrom-refl
d_AgreeMemFrom'45'refl_38 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_AgreeMemFrom'45'refl_38 = erased
-- Once.Arith.Backend.MemPreserveCore.AgreeMemFrom-trans
d_AgreeMemFrom'45'trans_54 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_AgreeMemFrom'45'trans_54 = erased
-- Once.Arith.Backend.MemPreserveCore.writeMem-below-preserves
d_writeMem'45'below'45'preserves_78 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeMem'45'below'45'preserves_78 = erased
-- Once.Arith.Backend.MemPreserveCore._.a≢addr
d_a'8802'addr_98 ::
  () ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Integer -> Integer -> AgdaAny) ->
  (AgdaAny ->
   Integer ->
   Integer ->
   Integer ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_a'8802'addr_98 = erased
