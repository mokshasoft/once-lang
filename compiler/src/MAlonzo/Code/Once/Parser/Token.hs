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

module MAlonzo.Code.Once.Parser.Token where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Parser.Token.Token
d_Token_6 = ()
data T_Token_6
  = C_TWord_8 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TInt_10 Integer |
    C_TString_12 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TLParen_14 | C_TRParen_16 | C_TLBrace_18 | C_TRBrace_20 |
    C_TColon_22 | C_TEquals_24 | C_TArrow_26 | C_TCaret1_28 |
    C_TCaret0_30 | C_TCaretW_32 | C_TLambda_34 | C_TComma_36 |
    C_TSemicolon_38 | C_TAt_40 | C_TPipe_42 | C_TDot_44 | C_TPlus_46 |
    C_TMinus_48 | C_TStar_50 | C_TSlash_52 | C_TPercent_54 |
    C_TAmpersand_56 | C_TLt_58 | C_TLe_60 | C_TGt_62 | C_TGe_64 |
    C_TEqEq_66 | C_TNeq_68 | C_TBang_70 | C_TNewline_72 | C_TEOF_74
