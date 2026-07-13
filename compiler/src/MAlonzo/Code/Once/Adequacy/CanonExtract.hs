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

module MAlonzo.Code.Once.Adequacy.CanonExtract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve

-- Once.Adequacy.CanonExtract.canonBody
d_canonBody_6 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96
d_canonBody_6 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.C_mkFunInfo_118
      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_funAlloc_112 (coe v1))
      (coe
         MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v1)))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v1))
-- Once.Adequacy.CanonExtract.canonFI
d_canonFI_12 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96
d_canonFI_12 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.C_mkFunInfo_118
      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_funAlloc_112 (coe v1))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v1))
         (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v1))))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v1))
-- Once.Adequacy.CanonExtract.canonFuns
d_canonFuns_18 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96]
d_canonFuns_18 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22 (coe d_canonFI_12 (coe v0))
-- Once.Adequacy.CanonExtract.canonPFI
d_canonPFI_22 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_120 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_120
d_canonPFI_22 v0 v1
  = coe
      MAlonzo.Code.Once.Parser.C_mkPolyFunInfo_138
      (coe MAlonzo.Code.Once.Parser.d_pfunName_130 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_pfunType_132 (coe v1))
      (coe MAlonzo.Code.Once.Parser.d_pfunAlloc_134 (coe v1))
      (coe
         MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Once.Parser.d_pfunBody_136 (coe v1)))
-- Once.Adequacy.CanonExtract.canonPolys
d_canonPolys_28 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120]
d_canonPolys_28 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22 (coe d_canonPFI_22 (coe v0))
-- Once.Adequacy.CanonExtract.extract-commute
d_extract'45'commute_44 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extract'45'commute_44 = erased
