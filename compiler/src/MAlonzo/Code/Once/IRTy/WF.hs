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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IRTy.WF.base-⌈⌉
d_base'45''8968''8969'_8 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_104 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'45''8968''8969'_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_base'45'Unit_106
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
      MAlonzo.Code.Once.IRTy.C_base'45'Void_108
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
      MAlonzo.Code.Once.IRTy.C_base'45'Int_110
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
      MAlonzo.Code.Once.IRTy.C_base'45'Float_112
        -> coe MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
      MAlonzo.Code.Once.IRTy.C_base'45'Prod_118 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_base'45'Sum_124 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112
                    (d_base'45''8968''8969'_8 (coe v6) (coe v4))
                    (d_base'45''8968''8969'_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌈⌉
d_wf'45''8968''8969'_20 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_126 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118
d_wf'45''8968''8969'_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_130 v3
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v4
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126
                    (d_base'45''8968''8969'_8 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_132
        -> coe MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_138 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_144 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C_wf'45''8855'_140
                    (d_wf'45''8968''8969'_20 (coe v6) (coe v4))
                    (d_wf'45''8968''8969'_20 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.base-⌊⌋
d_base'45''8970''8971'_38 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_104
d_base'45''8970''8971'_38 ~v0 ~v1 v2 v3
  = du_base'45''8970''8971'_38 v2 v3
du_base'45''8970''8971'_38 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_104
du_base'45''8970''8971'_38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'var_92
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_108
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Unit_106
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Void_108
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Int_110
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe MAlonzo.Code.Once.IRTy.C_base'45'Float_112
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Prod_118
                    (coe du_base'45''8970''8971'_38 (coe v6) (coe v4))
                    (coe du_base'45''8970''8971'_38 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_base'45'Sum_124
                    (coe du_base'45''8970''8971'_38 (coe v6) (coe v4))
                    (coe du_base'45''8970''8971'_38 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.WF.wf-⌊⌋
d_wf'45''8970''8971'_54 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_126
d_wf'45''8970''8971'_54 ~v0 ~v1 v2 v3
  = du_wf'45''8970''8971'_54 v2 v3
du_wf'45''8970''8971'_54 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_126
du_wf'45''8970''8971'_54 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_38 v4
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'K_130
                    (coe du_base'45''8970''8971'_38 (coe v4) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128
        -> coe MAlonzo.Code.Once.IRTy.C_wf'45'Id_132
      MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Sum_138
                    (coe du_wf'45''8970''8971'_54 (coe v6) (coe v4))
                    (coe du_wf'45''8970''8971'_54 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_wf'45''8855'_140 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v6 v7
               -> coe
                    MAlonzo.Code.Once.IRTy.C_wf'45'Prod_144
                    (coe du_wf'45''8970''8971'_54 (coe v6) (coe v4))
                    (coe du_wf'45''8970''8971'_54 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
