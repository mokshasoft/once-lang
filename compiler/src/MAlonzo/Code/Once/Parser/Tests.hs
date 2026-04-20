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

module MAlonzo.Code.Once.Parser.Tests where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- Once.Parser.Tests.parseType-empty-fails
d_parseType'45'empty'45'fails_6 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'empty'45'fails_6 = erased
-- Once.Parser.Tests.parseType-Unit
d_parseType'45'Unit_8 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Unit_8 = erased
-- Once.Parser.Tests.parseType-Void
d_parseType'45'Void_10 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Void_10 = erased
-- Once.Parser.Tests.parseType-Int
d_parseType'45'Int_12 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Int_12 = erased
-- Once.Parser.Tests.parseType-Float
d_parseType'45'Float_14 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Float_14 = erased
-- Once.Parser.Tests.parseType-Buffer
d_parseType'45'Buffer_16 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Buffer_16 = erased
-- Once.Parser.Tests.parseType-String
d_parseType'45'String_18 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'String_18 = erased
-- Once.Parser.Tests.parseType-Unit-leftover
d_parseType'45'Unit'45'leftover_20 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Unit'45'leftover_20 = erased
-- Once.Parser.Tests.parseType-Unit*Int
d_parseType'45'Unit'42'Int_22 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Unit'42'Int_22 = erased
-- Once.Parser.Tests.parseType-Int+Str
d_parseType'45'Int'43'Str_24 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Int'43'Str_24 = erased
-- Once.Parser.Tests.parseType-Int⇒Int-default
d_parseType'45'Int'8658'Int'45'default_26 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Int'8658'Int'45'default_26 = erased
-- Once.Parser.Tests.parseType-Int-linear-Int
d_parseType'45'Int'45'linear'45'Int_28 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Int'45'linear'45'Int_28 = erased
-- Once.Parser.Tests.parseType-Int-erased-Unit
d_parseType'45'Int'45'erased'45'Unit_30 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'Int'45'erased'45'Unit_30 = erased
-- Once.Parser.Tests.parseType-paren-Int
d_parseType'45'paren'45'Int_32 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'paren'45'Int_32 = erased
-- Once.Parser.Tests.parseType-arrow-alone
d_parseType'45'arrow'45'alone_34 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'arrow'45'alone_34 = erased
-- Once.Parser.Tests.parseType-star-alone
d_parseType'45'star'45'alone_36 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseType'45'star'45'alone_36 = erased
