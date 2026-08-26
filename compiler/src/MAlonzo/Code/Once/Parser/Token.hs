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
    C_TInt_10 Integer Integer |
    C_TFloat_12 Integer Integer Integer Integer |
    C_TString_14 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TLParen_16 | C_TRParen_18 | C_TLBrace_20 | C_TRBrace_22 |
    C_TColon_24 | C_TEquals_26 | C_TArrow_28 | C_TCaret1_30 |
    C_TCaret0_32 | C_TCaretW_34 | C_TLambda_36 | C_TComma_38 |
    C_TSemicolon_40 | C_TAt_42 | C_TPipe_44 | C_TDot_46 | C_TPlus_48 |
    C_TMinus_50 | C_TStar_52 | C_TSlash_54 | C_TPercent_56 |
    C_TAmpersand_58 | C_TLt_60 | C_TLe_62 | C_TGt_64 | C_TGe_66 |
    C_TEqEq_68 | C_TNeq_70 | C_TBang_72 | C_TNewline_74 | C_TEOF_76
