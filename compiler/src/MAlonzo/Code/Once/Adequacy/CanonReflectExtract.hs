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

module MAlonzo.Code.Once.Adequacy.CanonReflectExtract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve

-- Once.Adequacy.CanonReflectExtract.extract-commute-inj₁
d_extract'45'commute'45'inj'8321'_16 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extract'45'commute'45'inj'8321'_16 = erased
-- Once.Adequacy.CanonReflectExtract.distinctOrErr-inj₁-transfer-inj₂
d_distinctOrErr'45'inj'8321''45'transfer'45'inj'8322'_760 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distinctOrErr'45'inj'8321''45'transfer'45'inj'8322'_760 = erased
-- Once.Adequacy.CanonReflectExtract.extractFunctions-canon-inj₁
d_extractFunctions'45'canon'45'inj'8321'_768 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractFunctions'45'canon'45'inj'8321'_768 = erased
-- Once.Adequacy.CanonReflectExtract._.al
d_al_780 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_al_780 v0 ~v1 ~v2 = du_al_780 v0
du_al_780 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_al_780 v0
  = coe
      MAlonzo.Code.Once.Parser.d_extractAliases_76
      (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v0))
-- Once.Adequacy.CanonReflectExtract._.b
d_b_782 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_b_782 v0 ~v1 ~v2 = du_b_782 v0
du_b_782 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_b_782 v0
  = coe
      MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_314 (coe v0)
-- Once.Adequacy.CanonReflectExtract._.aux
d_aux_786 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_aux_786 = erased
