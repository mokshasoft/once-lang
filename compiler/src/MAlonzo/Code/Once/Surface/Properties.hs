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

module MAlonzo.Code.Once.Surface.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Properties.≤q-refl
d_'8804'q'45'refl_8 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'refl_8 = erased
-- Once.Surface.Properties.≤q-trans
d_'8804'q'45'trans_16 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'trans_16 = erased
-- Once.Surface.Properties.+q-comm
d_'43'q'45'comm_68 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'comm_68 = erased
-- Once.Surface.Properties.+q-assoc
d_'43'q'45'assoc_76 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'assoc_76 = erased
-- Once.Surface.Properties.+q-identityˡ
d_'43'q'45'identity'737'_92 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'737'_92 = erased
-- Once.Surface.Properties.+q-identityʳ
d_'43'q'45'identity'691'_98 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'691'_98 = erased
-- Once.Surface.Properties.+q-absorb
d_'43'q'45'absorb_102 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'absorb_102 = erased
-- Once.Surface.Properties.+ᵘ-comm
d_'43''7512''45'comm_112 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'comm_112 = erased
-- Once.Surface.Properties.+ᵘ-assoc
d_'43''7512''45'assoc_130 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'assoc_130 = erased
-- Once.Surface.Properties.+ᵘ-identityˡ
d_'43''7512''45'identity'737'_148 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'identity'737'_148 = erased
-- Once.Surface.Properties.+ᵘ-identityʳ
d_'43''7512''45'identity'691'_158 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'identity'691'_158 = erased
-- Once.Surface.Properties.*ᵘ-identityˡ
d_'42''7512''45'identity'737'_168 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'identity'737'_168 = erased
-- Once.Surface.Properties.*ᵘ-zeroˡ
d_'42''7512''45'zero'737'_180 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'zero'737'_180 = erased
-- Once.Surface.Properties.*ᵘ-zeroʳ
d_'42''7512''45'zero'691'_190 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'zero'691'_190 = erased
-- Once.Surface.Properties.≤ᵘ?-refl
d_'8804''7512''63''45'refl_204 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''7512''63''45'refl_204 = erased
-- Once.Surface.Properties.≤ᵘ?-zero
d_'8804''7512''63''45'zero_218 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''7512''63''45'zero_218 = erased
