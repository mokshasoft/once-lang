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

module MAlonzo.Code.Once.Spec.Grammar.FunDef where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Parser.ExprRelation
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Spec.Grammar.FunDef.ParsesParams
d_ParsesParams_8 a0 a1 a2 = ()
data T_ParsesParams_8
  = C_pp'45'eq_14 | C_pp'45'cons_24 T_ParsesParams_8 |
    C_pp'45'stop_30 | C_pp'45'noword_34
-- Once.Spec.Grammar.FunDef.ParsesFunBody
d_ParsesFunBody_42 a0 a1 a2 a3 a4 a5 = ()
data T_ParsesFunBody_42
  = C_pfb'45'mk_56 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                   MAlonzo.Code.Once.Parser.ExprRelation.T_ParsesExpr_498
-- Once.Spec.Grammar.FunDef.ParsesAlloc
d_ParsesAlloc_58 a0 a1 a2 = ()
data T_ParsesAlloc_58 = C_pa'45'some_64 | C_pa'45'none_68
-- Once.Spec.Grammar.FunDef.ParsesFunDef
d_ParsesFunDef_72 a0 a1 a2 a3 = ()
data T_ParsesFunDef_72
  = C_pfd'45'mk_90 (Maybe
                      MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                   [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                   [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                   [MAlonzo.Code.Once.Parser.Token.T_Token_6] T_ParsesAlloc_58
                   T_ParsesParams_8 T_ParsesFunBody_42
