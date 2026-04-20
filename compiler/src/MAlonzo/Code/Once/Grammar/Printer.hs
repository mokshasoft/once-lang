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

module MAlonzo.Code.Once.Grammar.Printer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.Printer.quantityToken
d_quantityToken_6 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6
d_quantityToken_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_30
      MAlonzo.Code.Once.Type.C_One_8
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_28
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Printer.printGType
d_printGType_8 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_printGType_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Unit" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TVoid_12
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Void" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TInt_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Int" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TFloat_16
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Float" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TBuffer_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Buffer" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TString_20
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("String" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__22 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe d_quantityToken_6 (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_26)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe d_printGType_8 (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      MAlonzo.Code.Once.Grammar.C__'8855'__24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TStar_50)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C__'8853'__26 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_46)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_TEff_28 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TWord_8
                   (coe ("Eff" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGType_8 (coe v1))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_TVar_30 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Printer.round-trip-Unit
d_round'45'trip'45'Unit_30 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Unit_30 = erased
-- Once.Grammar.Printer.round-trip-Void
d_round'45'trip'45'Void_32 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Void_32 = erased
-- Once.Grammar.Printer.round-trip-Int
d_round'45'trip'45'Int_34 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int_34 = erased
-- Once.Grammar.Printer.round-trip-Float
d_round'45'trip'45'Float_36 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Float_36 = erased
-- Once.Grammar.Printer.round-trip-Buffer
d_round'45'trip'45'Buffer_38 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Buffer_38 = erased
-- Once.Grammar.Printer.round-trip-String
d_round'45'trip'45'String_40 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'String_40 = erased
-- Once.Grammar.Printer.round-trip-Unit⊗Int-smoke
d_round'45'trip'45'Unit'8855'Int'45'smoke_42 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Unit'8855'Int'45'smoke_42 = erased
-- Once.Grammar.Printer.round-trip-Int⊕Str-smoke
d_round'45'trip'45'Int'8853'Str'45'smoke_44 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int'8853'Str'45'smoke_44 = erased
-- Once.Grammar.Printer.round-trip-Int⇒Int-smoke
d_round'45'trip'45'Int'8658'Int'45'smoke_46 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int'8658'Int'45'smoke_46 = erased
-- Once.Grammar.Printer.round-trip-linear-smoke
d_round'45'trip'45'linear'45'smoke_48 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'linear'45'smoke_48 = erased
-- Once.Grammar.Printer.round-trip-erased-smoke
d_round'45'trip'45'erased'45'smoke_50 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'erased'45'smoke_50 = erased
-- Once.Grammar.Printer.round-trip-nested-product-smoke
d_round'45'trip'45'nested'45'product'45'smoke_52 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'nested'45'product'45'smoke_52 = erased
-- Once.Grammar.Printer.round-trip-arrow-into-product-smoke
d_round'45'trip'45'arrow'45'into'45'product'45'smoke_54 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'arrow'45'into'45'product'45'smoke_54 = erased
-- Once.Grammar.Printer.round-trip-curried-linear-smoke
d_round'45'trip'45'curried'45'linear'45'smoke_56 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'curried'45'linear'45'smoke_56 = erased
-- Once.Grammar.Printer.round-trip-sum-of-arrows-smoke
d_round'45'trip'45'sum'45'of'45'arrows'45'smoke_58 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'sum'45'of'45'arrows'45'smoke_58 = erased
-- Once.Grammar.Printer.Concrete
d_Concrete_60 a0 = ()
data T_Concrete_60
  = C_c'45'unit_62 | C_c'45'void_64 | C_c'45'int_66 |
    C_c'45'float_68 | C_c'45'buffer_70 | C_c'45'string_72 |
    C_c'45'prod_78 T_Concrete_60 T_Concrete_60 |
    C_c'45'sum_84 T_Concrete_60 T_Concrete_60 |
    C_c'45'fun_92 T_Concrete_60 T_Concrete_60 |
    C_c'45'eff_98 T_Concrete_60 T_Concrete_60
