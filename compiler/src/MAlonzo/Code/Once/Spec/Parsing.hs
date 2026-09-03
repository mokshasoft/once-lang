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

module MAlonzo.Code.Once.Spec.Parsing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grammar.Decl

-- Once.Spec.Parsing.ParsesDecls
d_ParsesDecls_6 a0 a1 a2 = ()
data T_ParsesDecls_6
  = C_pds'45'noskip_10 |
    C_pds'45'stop_18 [MAlonzo.Code.Once.Parser.Token.T_Token_6] |
    C_pds'45'cons_34 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Spec.Grammar.Decl.T_ParsesDecl_8 T_ParsesDecls_6
-- Once.Spec.Parsing.ParsesModule
d_ParsesModule_36 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParsesModule_36 = erased
-- Once.Spec.Parsing.ParsesText
d_ParsesText_44 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> ()
d_ParsesText_44 = erased
