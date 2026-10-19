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

module MAlonzo.Code.Once.Lang.Principal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Typing.Scope

-- Once.Lang.Principal.gradesBelow
d_gradesBelow_6 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  [MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32]
d_gradesBelow_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.finBelow
d_finBelow_8 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  [MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40]
d_finBelow_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.lowerings
d_lowerings_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Lang.Type.T_Type_8]
d_lowerings_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v3 ->
                         coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v2)))
                   (coe d_lowerings_10 (coe v1)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v1))
                   (coe d_lowerings_10 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v3 ->
                         coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3) (coe v2)))
                   (coe d_lowerings_10 (coe v1)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v1))
                   (coe d_lowerings_10 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
                             (coe v2))
                          (coe d_lowerings_10 (coe v3)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v4)
                                     (coe v6))
                                  (coe v3)))
                          (coe d_gradesBelow_6 (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v1))
                (coe d_finBelow_8 (coe v2)))
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.PrincipalAt
d_PrincipalAt_52 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_PrincipalAt_52 = erased
