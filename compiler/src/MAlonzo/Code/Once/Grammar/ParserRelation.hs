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
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.ParserRelation.toType
d_toType_8 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Grammar.Printer.T_Concrete_60 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_toType_8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'unit_62
        -> coe MAlonzo.Code.Once.Type.C_Unit_118
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'void_64
        -> coe MAlonzo.Code.Once.Type.C_Void_120
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'int_66
        -> coe MAlonzo.Code.Once.Type.C_Int_132
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'float_68
        -> coe MAlonzo.Code.Once.Type.C_Float_134
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'buffer_70
        -> coe MAlonzo.Code.Once.Type.C_Buffer_138
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'string_72
        -> coe MAlonzo.Code.Once.Type.C_Str_136
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'prod_78 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8855'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.Type.C__'42'__122
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'sum_84 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8853'__26 v6 v7
               -> coe
                    MAlonzo.Code.Once.Type.C__'43'__124
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'fun_92 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                    (coe d_toType_8 (coe v7) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v8)
                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                    (coe d_toType_8 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.Printer.C_c'45'eff_98 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_TEff_28 v6 v7
               -> coe
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                    (coe d_toType_8 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                    (coe d_toType_8 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
