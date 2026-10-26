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

module MAlonzo.Code.Once.Format where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Format.Lex
import qualified MAlonzo.Code.Once.Format.Print
import qualified MAlonzo.Code.Once.Parser

-- Once.Format.formatParsed
d_formatParsed_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_formatParsed_4 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Once.Format.Print.d_format_1160 (coe v2)
                (coe
                   MAlonzo.Code.Once.Format.Lex.d_lexItems_518
                   (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.formatSource
d_formatSource_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_formatSource_14 v0
  = coe
      d_formatParsed_4 (coe v0)
      (coe MAlonzo.Code.Once.Parser.d_parseStrict_72 (coe v0))
