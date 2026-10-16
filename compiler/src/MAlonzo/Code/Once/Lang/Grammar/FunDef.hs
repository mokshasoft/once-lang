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

module MAlonzo.Code.Once.Lang.Grammar.FunDef where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Parser.ExprRelation
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Lang.Grammar.FunDef.ParsesParams
d_ParsesParams_8 a0 a1 a2 = ()
data T_ParsesParams_8
  = C_pp'45'eq_14 | C_pp'45'cons_24 T_ParsesParams_8 |
    C_pp'45'stop_30 | C_pp'45'noword_34
-- Once.Lang.Grammar.FunDef.ParsesFunBody
d_ParsesFunBody_40 a0 a1 a2 a3 a4 = ()
data T_ParsesFunBody_40
  = C_pfb'45'mk_52 MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
                   MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_500
-- Once.Lang.Grammar.FunDef.ParsesFunDef
d_ParsesFunDef_56 a0 a1 a2 a3 = ()
data T_ParsesFunDef_56
  = C_pfd'45'mk_70 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                   [MAlonzo.Code.Once.Parser.Token.T_Token_6] T_ParsesParams_8
                   T_ParsesFunBody_40
