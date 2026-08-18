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

module MAlonzo.Code.Once.Semantics.ValueIR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.ValueIR._.⟦_⟧
d_'10214'_'10215'_12 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_12 = erased
-- Once.Semantics.ValueIR.⟦_⟧ᴵ
d_'10214'_'10215''7477'_20 ::
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7477'_20 = erased
-- Once.Semantics.ValueIR.⟦_⟧Fᴵ
d_'10214'_'10215'F'7477'_24 ::
  () -> () -> MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> () -> ()
d_'10214'_'10215'F'7477'_24 = erased
-- Once.Semantics.ValueIR.base-coh
d_base'45'coh_32 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'coh_32 = erased
-- Once.Semantics.ValueIR.tF-coh
d_tF'45'coh_54 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tF'45'coh_54 = erased
-- Once.Semantics.ValueIR.coh
d_coh_68 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh_68 = erased
