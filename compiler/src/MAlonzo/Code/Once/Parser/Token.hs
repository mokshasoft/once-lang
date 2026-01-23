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
    C_TColon_22 | C_TEquals_24 | C_TArrow_26 | C_TLambda_28 |
    C_TComma_30 | C_TSemicolon_32 | C_TAt_34 | C_TPipe_36 | C_TDot_38 |
    C_TPlus_40 | C_TMinus_42 | C_TStar_44 | C_TSlash_46 |
    C_TPercent_48 | C_TLt_50 | C_TLe_52 | C_TGt_54 | C_TGe_56 |
    C_TEqEq_58 | C_TNeq_60 | C_TNewline_62 | C_TEOF_64
