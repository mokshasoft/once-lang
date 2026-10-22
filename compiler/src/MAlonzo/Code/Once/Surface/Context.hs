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

module MAlonzo.Code.Once.Surface.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Type.Grade

-- Once.Surface.Context.zeroUsage?
d_zeroUsage'63'_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63'_10 ~v0 v1 = du_zeroUsage'63'_10 v1
du_zeroUsage'63'_10 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
du_zeroUsage'63'_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe du_zeroUsage'63'_10 (coe v3)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.zeroUsage?-just
d_zeroUsage'63''45'just_24 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63''45'just_24 = erased
-- Once.Surface.Context._≤ᵘ?_
d__'8804''7512''63'__36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 -> Bool
d__'8804''7512''63'__36 ~v0 ~v1 v2 v3
  = du__'8804''7512''63'__36 v2 v3
du__'8804''7512''63'__36 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 -> Bool
du__'8804''7512''63'__36 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_36
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v6 v7
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Once.Type.Grade.d__'8804'q'7495'__6 (coe v3)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12))
                    (coe du__'8804''7512''63'__36 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
