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

module MAlonzo.Code.Once.Adequacy.ResolverBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Adequacy.CanonModule
import qualified MAlonzo.Code.Once.Parser.Module.Core

-- Once.Adequacy.ResolverBridge.resolver-preserves-typing
d_resolver'45'preserves'45'typing_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resolver'45'preserves'45'typing_16
  = coe
      MAlonzo.Code.Once.Adequacy.CanonModule.d_canon'45'preserves'45'typing_34
-- Once.Adequacy.ResolverBridge.resolver-reflects-typing
d_resolver'45'reflects'45'typing_26
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ResolverBridge.resolver-reflects-typing"
-- Once.Adequacy.ResolverBridge.resolver-preserves-trace
d_resolver'45'preserves'45'trace_36
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ResolverBridge.resolver-preserves-trace"
