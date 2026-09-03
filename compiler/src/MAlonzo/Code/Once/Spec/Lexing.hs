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

module MAlonzo.Code.Once.Spec.Lexing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Spec.Lexing.LexesChars
d_LexesChars_6 a0 a1 a2 = ()
data T_LexesChars_6
  = C_lex'45'eof_10 | C_lex'45'ws_20 T_LexesChars_6 |
    C_lex'45'nl'45'ind_30 T_LexesChars_6 |
    C_lex'45'nl_40 T_LexesChars_6 | C_lex'45'caret1_50 T_LexesChars_6 |
    C_lex'45'caret0_60 T_LexesChars_6 |
    C_lex'45'caretw_70 T_LexesChars_6 |
    C_lex'45'caret'45'gen_80 T_LexesChars_6 |
    C_lex'45'lcomment'45'ind_90 T_LexesChars_6 |
    C_lex'45'arrow'45'ind_100 T_LexesChars_6 |
    C_lex'45'minus_110 T_LexesChars_6 |
    C_lex'45'bcomment'45'ind_120 T_LexesChars_6 |
    C_lex'45'lbrace_130 T_LexesChars_6 |
    C_lex'45'le'45'ind_140 T_LexesChars_6 |
    C_lex'45'lt_150 T_LexesChars_6 |
    C_lex'45'ge'45'ind_160 T_LexesChars_6 |
    C_lex'45'gt_170 T_LexesChars_6 |
    C_lex'45'eqeq'45'ind_180 T_LexesChars_6 |
    C_lex'45'equals_190 T_LexesChars_6 |
    C_lex'45'neq'45'ind_200 T_LexesChars_6 |
    C_lex'45'bang_210 T_LexesChars_6 |
    C_lex'45'lparen_220 T_LexesChars_6 |
    C_lex'45'rparen_230 T_LexesChars_6 |
    C_lex'45'rbrace_240 T_LexesChars_6 |
    C_lex'45'colon_250 T_LexesChars_6 |
    C_lex'45'lambda_260 T_LexesChars_6 |
    C_lex'45'comma_270 T_LexesChars_6 |
    C_lex'45'semi_280 T_LexesChars_6 | C_lex'45'at_290 T_LexesChars_6 |
    C_lex'45'pipe_300 T_LexesChars_6 |
    C_lex'45'plus_310 T_LexesChars_6 |
    C_lex'45'star_320 T_LexesChars_6 |
    C_lex'45'slash_330 T_LexesChars_6 |
    C_lex'45'pct_340 T_LexesChars_6 | C_lex'45'amp_350 T_LexesChars_6 |
    C_lex'45'dot_360 T_LexesChars_6 |
    C_lex'45'string_376 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22 T_LexesChars_6 |
    C_lex'45'string'45'err_384 | C_lex'45'digit_394 T_LexesChars_6 |
    C_lex'45'float_410 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22 T_LexesChars_6 |
    C_lex'45'ident_420 T_LexesChars_6 |
    C_lex'45'skip_430 T_LexesChars_6
-- Once.Spec.Lexing.Lexes
d_Lexes_432 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Lexes_432 = erased
