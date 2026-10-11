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
import qualified MAlonzo.Code.Once.Spec.Type.Grade

-- Once.Surface.Context.zeroUsage?
d_zeroUsage'63'_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63'_10 ~v0 v1 = du_zeroUsage'63'_10 v1
du_zeroUsage'63'_10 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
du_zeroUsage'63'_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_48
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      MAlonzo.Code.Once.Spec.Context.C__'8759'__52 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe du_zeroUsage'63'_10 (coe v3)
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Context.zeroUsage?-just
d_zeroUsage'63''45'just_24 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zeroUsage'63''45'just_24 = erased
-- Once.Surface.Context._≤ᵘ?_
d__'8804''7512''63'__34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 -> Bool
d__'8804''7512''63'__34 ~v0 v1 v2 = du__'8804''7512''63'__34 v1 v2
du__'8804''7512''63'__34 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 -> Bool
du__'8804''7512''63'__34 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'91''93'_48
        -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      MAlonzo.Code.Once.Spec.Context.C__'8759'__52 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v6 v7 v8
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Once.Spec.Type.Grade.d__'8804'q__26 (coe v3) (coe v8))
                    (coe du__'8804''7512''63'__34 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
