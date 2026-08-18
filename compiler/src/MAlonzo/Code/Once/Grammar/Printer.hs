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
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
      MAlonzo.Code.Once.Type.C_One_8
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Printer.printGType
d_printGType_8 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_printGType_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_12
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Unit" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TVoid_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Void" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TInt_16
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Int" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TFloat_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Float" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TBuffer_20
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Buffer" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_TString_22
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("String" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__24 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe d_quantityToken_6 (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe d_printGType_8 (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      MAlonzo.Code.Once.Grammar.C__'8855'__26 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C__'8853'__28 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGType_8 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGType_8 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_TEff_30 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
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
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_GMu_32 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Mu" :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGFunctor_10 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.Grammar.C_TVar_34 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TWord_8 (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Printer.printGFunctor
d_printGFunctor_10 ::
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_printGFunctor_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_GFK_36 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Parser.Token.C_TWord_8
                   (coe ("K" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_printGType_8 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.Grammar.C_GFId_38
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TWord_8
                (coe ("Id" :: Data.Text.Text)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Grammar.C_GFSum_40 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGFunctor_10 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGFunctor_10 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Grammar.C_GFProd_42 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_printGFunctor_10 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe d_printGFunctor_10 (coe v2))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Printer.round-trip-Unit
d_round'45'trip'45'Unit_44 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Unit_44 = erased
-- Once.Grammar.Printer.round-trip-Void
d_round'45'trip'45'Void_46 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Void_46 = erased
-- Once.Grammar.Printer.round-trip-Int
d_round'45'trip'45'Int_48 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int_48 = erased
-- Once.Grammar.Printer.round-trip-Float
d_round'45'trip'45'Float_50 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Float_50 = erased
-- Once.Grammar.Printer.round-trip-Buffer
d_round'45'trip'45'Buffer_52 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Buffer_52 = erased
-- Once.Grammar.Printer.round-trip-String
d_round'45'trip'45'String_54 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'String_54 = erased
-- Once.Grammar.Printer.round-trip-Unit⊗Int-smoke
d_round'45'trip'45'Unit'8855'Int'45'smoke_56 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Unit'8855'Int'45'smoke_56 = erased
-- Once.Grammar.Printer.round-trip-Int⊕Str-smoke
d_round'45'trip'45'Int'8853'Str'45'smoke_58 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int'8853'Str'45'smoke_58 = erased
-- Once.Grammar.Printer.round-trip-Int⇒Int-smoke
d_round'45'trip'45'Int'8658'Int'45'smoke_60 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'Int'8658'Int'45'smoke_60 = erased
-- Once.Grammar.Printer.round-trip-linear-smoke
d_round'45'trip'45'linear'45'smoke_62 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'linear'45'smoke_62 = erased
-- Once.Grammar.Printer.round-trip-erased-smoke
d_round'45'trip'45'erased'45'smoke_64 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'erased'45'smoke_64 = erased
-- Once.Grammar.Printer.round-trip-nested-product-smoke
d_round'45'trip'45'nested'45'product'45'smoke_66 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'nested'45'product'45'smoke_66 = erased
-- Once.Grammar.Printer.round-trip-arrow-into-product-smoke
d_round'45'trip'45'arrow'45'into'45'product'45'smoke_68 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'arrow'45'into'45'product'45'smoke_68 = erased
-- Once.Grammar.Printer.round-trip-curried-linear-smoke
d_round'45'trip'45'curried'45'linear'45'smoke_70 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'curried'45'linear'45'smoke_70 = erased
-- Once.Grammar.Printer.round-trip-sum-of-arrows-smoke
d_round'45'trip'45'sum'45'of'45'arrows'45'smoke_72 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'sum'45'of'45'arrows'45'smoke_72 = erased
-- Once.Grammar.Printer.Concrete
d_Concrete_74 a0 = ()
data T_Concrete_74
  = C_c'45'unit_76 | C_c'45'void_78 | C_c'45'int_80 |
    C_c'45'float_82 | C_c'45'buffer_84 | C_c'45'string_86 |
    C_c'45'prod_92 T_Concrete_74 T_Concrete_74 |
    C_c'45'sum_98 T_Concrete_74 T_Concrete_74 |
    C_c'45'fun_106 T_Concrete_74 T_Concrete_74 |
    C_c'45'eff_112 T_Concrete_74 T_Concrete_74
