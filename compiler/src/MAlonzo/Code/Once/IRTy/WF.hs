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
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_100 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_base'45''8968''8969'_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_base'45'Unit_102
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
      MAlonzo.Code.Once.IRTy.C_base'45'Void_104
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200
      MAlonzo.Code.Once.IRTy.C_base'45'Int_106
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202
      MAlonzo.Code.Once.IRTy.C_base'45'Float_108
        -> coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204
      MAlonzo.Code.Once.IRTy.C_base'45'Prod_114 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_base'45'Sum_120 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌈⌉
d_wf'45''8968''8969'_20 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236
d_wf'45''8968''8969'_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v3
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v4
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240
                    (d_base'45''8968''8969'_8 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.base-⌊⌋
d_base'45''8970''8971'_34 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_100
d_base'45''8970''8971'_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Unit_102
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_104
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Int_106
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Float_108
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Prod_114
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Sum_120
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'rigid_220
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_104
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌊⌋
d_wf'45''8970''8971'_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122
d_wf'45''8970''8971'_46 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v4
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'K_126
                    (d_base'45''8970''8971'_34 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
        -> coe MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
