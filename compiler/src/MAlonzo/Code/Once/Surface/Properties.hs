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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Surface.Properties.≤q-refl
d_'8804'q'45'refl_8 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'refl_8 = erased
-- Once.Surface.Properties.≤q-trans
d_'8804'q'45'trans_16 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'trans_16 = erased
-- Once.Surface.Properties.+q-comm
d_'43'q'45'comm_68 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'comm_68 = erased
-- Once.Surface.Properties.+q-assoc
d_'43'q'45'assoc_76 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'assoc_76 = erased
-- Once.Surface.Properties.+q-identityˡ
d_'43'q'45'identity'737'_80 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'737'_80 = erased
-- Once.Surface.Properties.+q-identityʳ
d_'43'q'45'identity'691'_84 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'identity'691'_84 = erased
-- Once.Surface.Properties.+q-absorb
d_'43'q'45'absorb_88 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'q'45'absorb_88 = erased
-- Once.Surface.Properties.+ᵘ-comm
d_'43''7512''45'comm_98 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'comm_98 = erased
-- Once.Surface.Properties.+ᵘ-assoc
d_'43''7512''45'assoc_116 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'assoc_116 = erased
-- Once.Surface.Properties.+ᵘ-identityˡ
d_'43''7512''45'identity'737'_134 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'identity'737'_134 = erased
-- Once.Surface.Properties.+ᵘ-identityʳ
d_'43''7512''45'identity'691'_144 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'identity'691'_144 = erased
-- Once.Surface.Properties.*ᵘ-identityˡ
d_'42''7512''45'identity'737'_154 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'identity'737'_154 = erased
-- Once.Surface.Properties.*ᵘ-zeroˡ
d_'42''7512''45'zero'737'_166 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'zero'737'_166 = erased
-- Once.Surface.Properties.*ᵘ-zeroʳ
d_'42''7512''45'zero'691'_176 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''7512''45'zero'691'_176 = erased
-- Once.Surface.Properties.≤ᵘ?-refl
d_'8804''7512''63''45'refl_190 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''7512''63''45'refl_190 = erased
-- Once.Surface.Properties.≤ᵘ?-zero
d_'8804''7512''63''45'zero_204 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''7512''63''45'zero_204 = erased
-- Once.Surface.Properties.+ᵘ-idʳ
d_'43''7512''45'id'691'_218 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''7512''45'id'691'_218 = erased
-- Once.Surface.Properties.erase-arg-usage
d_erase'45'arg'45'usage_230 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'45'arg'45'usage_230 = erased
