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

module MAlonzo.Code.Once.Spec.Grammar.OpDecl where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grammar.FunDef
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Grammar.OpDecl.ParsesOpChars
d_ParsesOpChars_8 a0 a1 a2 a3 = ()
data T_ParsesOpChars_8
  = C_poc'45'close_18 |
    C_poc'45'char_32 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                     T_ParsesOpChars_8
-- Once.Spec.Grammar.OpDecl.ParsesOpAfter
d_ParsesOpAfter_36 a0 a1 a2 a3 = ()
data T_ParsesOpAfter_36
  = C_poa'45'sig_46 MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 |
    C_poa'45'fun_54 MAlonzo.Code.Once.Spec.Grammar.FunDef.T_ParsesFunDef_72
-- Once.Spec.Grammar.OpDecl.ParsesOpDecl
d_ParsesOpDecl_56 a0 a1 a2 = ()
data T_ParsesOpDecl_56
  = C_pod'45'mk_68 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   [MAlonzo.Code.Once.Parser.Token.T_Token_6] T_ParsesOpChars_8
                   T_ParsesOpAfter_36
