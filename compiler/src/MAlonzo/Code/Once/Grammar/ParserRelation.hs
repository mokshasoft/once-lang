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

module MAlonzo.Code.Once.Grammar.ParserRelation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.Printer
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Grammar.ParserRelation.toType
d_toType_8 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_78 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_toType_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'unit_80
        -> coe MAlonzo.Code.Once.Lang.Type.C_Unit_20
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'void_82
        -> coe MAlonzo.Code.Once.Lang.Type.C_Void_22
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'int_84
        -> coe MAlonzo.Code.Once.Lang.Type.C_Int_34
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'float_86
        -> coe MAlonzo.Code.Once.Lang.Type.C_Float_36
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'prod_92 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8855'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'sum_98 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8853'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'fun_106 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__20 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                    (coe d_toType_8 (coe v7) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v8)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    (coe d_toType_8 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'eff_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_TEff_26 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'act_118 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_TAct_28 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
