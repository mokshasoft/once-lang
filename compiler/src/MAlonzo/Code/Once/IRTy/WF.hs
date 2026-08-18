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
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_88 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_base'45''8968''8969'_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_base'45'Unit_90
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
      MAlonzo.Code.Once.IRTy.C_base'45'Void_92
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
      MAlonzo.Code.Once.IRTy.C_base'45'Int_94
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
      MAlonzo.Code.Once.IRTy.C_base'45'Float_96
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
      MAlonzo.Code.Once.IRTy.C_base'45'Str_98
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
      MAlonzo.Code.Once.IRTy.C_base'45'Buffer_100
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
      MAlonzo.Code.Once.IRTy.C_base'45'Prod_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_base'45'Sum_112 v4 v5
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
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
d_wf'45''8968''8969'_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_118 v3
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v4
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244
                    (d_base'45''8968''8969'_8 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_120
        -> coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132 v4 v5
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_88
d_base'45''8970''8971'_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Unit_90
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_92
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Int_94
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Float_96
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Str_98
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Buffer_100
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Prod_106
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Sum_112
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌊⌋
d_wf'45''8970''8971'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
d_wf'45''8970''8971'_46 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v4
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'K_118
                    (d_base'45''8970''8971'_34 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246
        -> coe MAlonzo.Code.Once.IRTy.C_wf'45'Id_120
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
