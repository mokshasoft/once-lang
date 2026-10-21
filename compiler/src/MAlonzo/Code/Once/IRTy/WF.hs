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
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed

-- Once.IRTy.WF.base-⌈⌉
d_base'45''8968''8969'_8 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_100 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8
d_base'45''8968''8969'_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_base'45'Unit_102
        -> coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10
      MAlonzo.Code.Once.IRTy.C_base'45'Void_104
        -> coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Void_12
      MAlonzo.Code.Once.IRTy.C_base'45'Int_106
        -> coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Int_14
      MAlonzo.Code.Once.IRTy.C_base'45'Float_108
        -> coe
             MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Float_16
      MAlonzo.Code.Once.IRTy.C_base'45'Prod_114 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
               -> coe
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Prod_22
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_base'45'Sum_120 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Sum_28
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌈⌉
d_wf'45''8968''8969'_20 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48
d_wf'45''8968''8969'_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v3
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v4
               -> coe
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52
                    (d_base'45''8968''8969'_8 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.base-⌊⌋
d_base'45''8970''8971'_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_100
d_base'45''8970''8971'_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Unit_102
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Void_12
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_104
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Int_14
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Int_106
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Float_16
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Float_108
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Prod_22 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Prod_114
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Sum_28 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Sum_120
                    (d_base'45''8970''8971'_34 (coe v6) (coe v4))
                    (d_base'45''8970''8971'_34 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'rigid_32
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_104
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌊⌋
d_wf'45''8970''8971'_46 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122
d_wf'45''8970''8971'_46 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v4
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'K_126
                    (d_base'45''8970''8971'_34 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54
        -> coe MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140
                    (d_wf'45''8970''8971'_46 (coe v6) (coe v4))
                    (d_wf'45''8970''8971'_46 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
