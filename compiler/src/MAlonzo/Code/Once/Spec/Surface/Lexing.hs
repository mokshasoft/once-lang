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

module MAlonzo.Code.Once.Spec.Surface.Lexing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base

-- Once.Spec.Surface.Lexing.Token
d_Token_8 = ()
data T_Token_8
  = C_TWord_10 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TInt_12 Integer | C_TFloat_14 Integer Integer Integer |
    C_TString_16 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TLParen_18 | C_TRParen_20 | C_TLBrace_22 | C_TRBrace_24 |
    C_TColon_26 | C_TEquals_28 | C_TArrow_30 | C_TCaret1_32 |
    C_TCaret0_34 | C_TCaretW_36 | C_TLambda_38 | C_TComma_40 |
    C_TSemicolon_42 | C_TAt_44 | C_TPipe_46 | C_TDot_48 | C_TPlus_50 |
    C_TMinus_52 | C_TStar_54 | C_TSlash_56 | C_TPercent_58 |
    C_TAmpersand_60 | C_TLt_62 | C_TLe_64 | C_TGt_66 | C_TGe_68 |
    C_TEqEq_70 | C_TNeq_72 | C_TBang_74 | C_TNewline_76 | C_TEOF_78
-- Once.Spec.Surface.Lexing.code
d_code_80 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_code_80 = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
-- Once.Spec.Surface.Lexing.isIdentStart
d_isIdentStart_82 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentStart_82 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe eqInt (coe d_code_80 v0) (coe d_code_80 '_'))
-- Once.Spec.Surface.Lexing.isIdentContinue
d_isIdentContinue_86 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentContinue_86 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe eqInt (coe d_code_80 v0) (coe d_code_80 '_'))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe eqInt (coe d_code_80 v0) (coe d_code_80 '\''))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe eqInt (coe d_code_80 v0) (coe d_code_80 '+'))
                  (coe
                     MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                     (coe eqInt (coe d_code_80 v0) (coe d_code_80 '*'))
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe eqInt (coe d_code_80 v0) (coe d_code_80 '!'))
                        (coe eqInt (coe d_code_80 v0) (coe d_code_80 '?'))))))))
-- Once.Spec.Surface.Lexing.digitsToNat
d_digitsToNat_90 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_90 = coe d_go_96 (coe (0 :: Integer))
-- Once.Spec.Surface.Lexing._.go
d_go_96 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_go_96 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_go_96
             (coe
                addInt
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_code_80 v2)
                   (coe d_code_80 '0'))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Lexing.Special
d_Special_106 a0 = ()
data T_Special_106
  = C_sp'45'space_108 | C_sp'45'tab_110 | C_sp'45'cr_112 |
    C_sp'45'nl_114 | C_sp'45'backslash_116 | C_sp'45'caret_118 |
    C_sp'45'dash_120 | C_sp'45'lbrace_122 | C_sp'45'lt_124 |
    C_sp'45'gt_126 | C_sp'45'eq_128 | C_sp'45'bang_130 |
    C_sp'45'lparen_132 | C_sp'45'rparen_134 | C_sp'45'rbrace_136 |
    C_sp'45'colon_138 | C_sp'45'comma_140 | C_sp'45'semi_142 |
    C_sp'45'at_144 | C_sp'45'pipe_146 | C_sp'45'plus_148 |
    C_sp'45'star_150 | C_sp'45'slash_152 | C_sp'45'pct_154 |
    C_sp'45'amp_156 | C_sp'45'dot_158 | C_sp'45'quote_160
-- Once.Spec.Surface.Lexing.Next
d_Next_162 a0 a1 = ()
data T_Next_162 = C_next_168
-- Once.Spec.Surface.Lexing.Digits
d_Digits_170 a0 a1 a2 = ()
data T_Digits_170
  = C_dg'45'end_172 | C_dg'45'stop_178 |
    C_dg'45'more_188 T_Digits_170
-- Once.Spec.Surface.Lexing.Fraction
d_Fraction_190 a0 a1 a2 = ()
newtype T_Fraction_190 = C_fraction_200 T_Digits_170
-- Once.Spec.Surface.Lexing.IdentRest
d_IdentRest_202 a0 a1 a2 = ()
data T_IdentRest_202
  = C_id'45'end_204 | C_id'45'stop_210 |
    C_id'45'more_220 T_IdentRest_202
-- Once.Spec.Surface.Lexing.Escape
d_Escape_222 a0 a1 = ()
data T_Escape_222
  = C_esc'45'n_224 | C_esc'45't_226 | C_esc'45'r_228 |
    C_esc'45'bs_230 | C_esc'45'q_232
-- Once.Spec.Surface.Lexing.StringBody
d_StringBody_234 a0 a1 a2 = ()
data T_StringBody_234
  = C_sb'45'close_238 |
    C_sb'45'esc_250 T_Escape_222 T_StringBody_234 |
    C_sb'45'char_264 T_StringBody_234
-- Once.Spec.Surface.Lexing.LineRest
d_LineRest_266 a0 a1 = ()
data T_LineRest_266
  = C_lr'45'end_268 | C_lr'45'nl_272 |
    C_lr'45'char_280 T_LineRest_266
-- Once.Spec.Surface.Lexing.BlockRest
d_BlockRest_282 a0 a1 a2 = ()
data T_BlockRest_282
  = C_br'45'done_286 | C_br'45'end_290 | C_br'45'last_296 |
    C_br'45'open_304 T_BlockRest_282 |
    C_br'45'close_312 T_BlockRest_282 |
    C_br'45'char_324 T_BlockRest_282
-- Once.Spec.Surface.Lexing.LexesChars
d_LexesChars_326 a0 a1 = ()
data T_LexesChars_326
  = C_lex'45'eof_328 | C_lex'45'space_334 T_LexesChars_326 |
    C_lex'45'tab_340 T_LexesChars_326 |
    C_lex'45'cr_346 T_LexesChars_326 |
    C_lex'45'nl'45'cont_354 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                            T_Next_162 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                            T_LexesChars_326 |
    C_lex'45'nl_360 T_LexesChars_326 |
    C_lex'45'caret1_366 T_LexesChars_326 |
    C_lex'45'caret0_372 T_LexesChars_326 |
    C_lex'45'caretw_378 T_LexesChars_326 |
    C_lex'45'caret_384 T_LexesChars_326 |
    C_lex'45'comment_392 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                         T_LineRest_266 T_LexesChars_326 |
    C_lex'45'arrow_398 T_LexesChars_326 |
    C_lex'45'minus_404 T_LexesChars_326 |
    C_lex'45'block_412 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       T_BlockRest_282 T_LexesChars_326 |
    C_lex'45'lbrace_418 T_LexesChars_326 |
    C_lex'45'le_424 T_LexesChars_326 |
    C_lex'45'lt_430 T_LexesChars_326 |
    C_lex'45'ge_436 T_LexesChars_326 |
    C_lex'45'gt_442 T_LexesChars_326 |
    C_lex'45'eqeq_448 T_LexesChars_326 |
    C_lex'45'equal_454 T_LexesChars_326 |
    C_lex'45'neq_460 T_LexesChars_326 |
    C_lex'45'bang_466 T_LexesChars_326 |
    C_lex'45'lparen_472 T_LexesChars_326 |
    C_lex'45'rparen_478 T_LexesChars_326 |
    C_lex'45'rbrace_484 T_LexesChars_326 |
    C_lex'45'colon_490 T_LexesChars_326 |
    C_lex'45'lambda_496 T_LexesChars_326 |
    C_lex'45'comma_502 T_LexesChars_326 |
    C_lex'45'semi_508 T_LexesChars_326 |
    C_lex'45'at_514 T_LexesChars_326 |
    C_lex'45'pipe_520 T_LexesChars_326 |
    C_lex'45'plus_526 T_LexesChars_326 |
    C_lex'45'star_532 T_LexesChars_326 |
    C_lex'45'slash_538 T_LexesChars_326 |
    C_lex'45'pct_544 T_LexesChars_326 |
    C_lex'45'amp_550 T_LexesChars_326 |
    C_lex'45'dot_556 T_LexesChars_326 |
    C_lex'45'string_566 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_StringBody_234
                        T_LexesChars_326 |
    C_lex'45'string'45'end_574 |
    C_lex'45'int_590 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                     [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_170
                     T_LexesChars_326 |
    C_lex'45'float_606 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_170
                       T_Fraction_190 T_LexesChars_326 |
    C_lex'45'ident_618 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_IdentRest_202
                       T_LexesChars_326 |
    C_lex'45'skip_626 T_LexesChars_326
-- Once.Spec.Surface.Lexing.Lexes
d_Lexes_628 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> [T_Token_8] -> ()
d_Lexes_628 = erased
