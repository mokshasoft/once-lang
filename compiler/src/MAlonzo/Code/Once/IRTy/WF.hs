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

module MAlonzo.Code.Once.IRTy.WF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.IRTy.WF.base-⌈⌉
d_base'45''8968''8969'_8 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_104 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45''8968''8969'_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_base'45'Unit_106
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
      MAlonzo.Code.Once.IRTy.C_base'45'Void_108
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
      MAlonzo.Code.Once.IRTy.C_base'45'Int_110
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
      MAlonzo.Code.Once.IRTy.C_base'45'Float_112
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
      MAlonzo.Code.Once.IRTy.C_base'45'Str_114
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
      MAlonzo.Code.Once.IRTy.C_base'45'Buffer_116
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
      MAlonzo.Code.Once.IRTy.C_base'45'Prod_122 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_base'45'Sum_128 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌈⌉
d_wf'45''8968''8969'_20 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
d_wf'45''8968''8969'_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_134 v3
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v4
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244
                    (d_base'45''8968''8969'_8 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_136
        -> coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_142 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_148 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.base-⌊⌋
d_base'45''8970''8971'_34 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_104
d_base'45''8970''8971'_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Unit_106
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_108
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Int_110
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Float_112
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Str_114
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Buffer_116
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Prod_122
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Sum_128
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌊⌋
d_wf'45''8970''8971'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
d_wf'45''8970''8971'_46 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'K_134
                    (d_base'45''8970''8971'_34 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246
        -> coe MAlonzo.Code.Once.IRTy.C_wf'45'Id_136
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__114 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Sum_142
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__116 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Prod_148
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
