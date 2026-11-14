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
import qualified MAlonzo.Code.Once.Spec.Surface.Operator

-- Once.Spec.Surface.Lexing.Token
d_Token_8 = ()
data T_Token_8
  = C_TWord_10 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TInt_12 Integer | C_TFloat_14 Integer Integer Integer |
    C_TString_16 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_TLParen_18 | C_TRParen_20 | C_TLBrace_22 | C_TRBrace_24 |
    C_TColon_26 | C_TEquals_28 | C_TArrow_30 | C_TCaret1_32 |
    C_TCaret0_34 | C_TCaretW_36 | C_TLambda_38 | C_TComma_40 |
    C_TSemicolon_42 | C_TAt_44 | C_TPipe_46 | C_TDot_48 |
    C_TAmpersand_50 | C_TBang_52 |
    C_TOp_54 MAlonzo.Code.Once.Spec.Surface.Operator.T_Op_30 |
    C_TOpD_56 MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 |
    C_TNewline_58 | C_TEOF_60
-- Once.Spec.Surface.Lexing.code
d_code_62 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_code_62 = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
-- Once.Spec.Surface.Lexing.isIdentStart
d_isIdentStart_64 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentStart_64 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe eqInt (coe d_code_62 v0) (coe d_code_62 '_'))
-- Once.Spec.Surface.Lexing.isIdentContinue
d_isIdentContinue_68 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentContinue_68 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe eqInt (coe d_code_62 v0) (coe d_code_62 '_'))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe eqInt (coe d_code_62 v0) (coe d_code_62 '\''))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe eqInt (coe d_code_62 v0) (coe d_code_62 '+'))
                  (coe
                     MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                     (coe eqInt (coe d_code_62 v0) (coe d_code_62 '*'))
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe eqInt (coe d_code_62 v0) (coe d_code_62 '!'))
                        (coe eqInt (coe d_code_62 v0) (coe d_code_62 '?'))))))))
-- Once.Spec.Surface.Lexing.digitsFrom
d_digitsFrom_72 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsFrom_72 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_digitsFrom_72
             (coe
                addInt
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_code_62 v2)
                   (coe d_code_62 '0'))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Lexing.digitsToNat
d_digitsToNat_82 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_82 = coe d_digitsFrom_72 (coe (0 :: Integer))
-- Once.Spec.Surface.Lexing.Special
d_Special_84 a0 = ()
data T_Special_84
  = C_sp'45'space_86 | C_sp'45'tab_88 | C_sp'45'cr_90 |
    C_sp'45'nl_92 | C_sp'45'backslash_94 | C_sp'45'caret_96 |
    C_sp'45'dash_98 | C_sp'45'lbrace_100 | C_sp'45'lt_102 |
    C_sp'45'gt_104 | C_sp'45'eq_106 | C_sp'45'bang_108 |
    C_sp'45'lparen_110 | C_sp'45'rparen_112 | C_sp'45'rbrace_114 |
    C_sp'45'colon_116 | C_sp'45'comma_118 | C_sp'45'semi_120 |
    C_sp'45'at_122 | C_sp'45'pipe_124 | C_sp'45'plus_126 |
    C_sp'45'star_128 | C_sp'45'slash_130 | C_sp'45'pct_132 |
    C_sp'45'amp_134 | C_sp'45'dot_136 | C_sp'45'quote_138
-- Once.Spec.Surface.Lexing.Next
d_Next_140 a0 a1 = ()
data T_Next_140 = C_next_146
-- Once.Spec.Surface.Lexing.Digits
d_Digits_148 a0 a1 a2 = ()
data T_Digits_148
  = C_dg'45'end_150 | C_dg'45'stop_156 |
    C_dg'45'more_166 T_Digits_148
-- Once.Spec.Surface.Lexing.Fraction
d_Fraction_168 a0 a1 a2 = ()
newtype T_Fraction_168 = C_fraction_178 T_Digits_148
-- Once.Spec.Surface.Lexing.IdentRest
d_IdentRest_180 a0 a1 a2 = ()
data T_IdentRest_180
  = C_id'45'end_182 | C_id'45'stop_188 |
    C_id'45'more_198 T_IdentRest_180
-- Once.Spec.Surface.Lexing.Escape
d_Escape_200 a0 a1 = ()
data T_Escape_200
  = C_esc'45'n_202 | C_esc'45't_204 | C_esc'45'r_206 |
    C_esc'45'bs_208 | C_esc'45'q_210
-- Once.Spec.Surface.Lexing.StringBody
d_StringBody_212 a0 a1 a2 = ()
data T_StringBody_212
  = C_sb'45'close_216 |
    C_sb'45'esc_228 T_Escape_200 T_StringBody_212 |
    C_sb'45'char_242 T_StringBody_212
-- Once.Spec.Surface.Lexing.LineRest
d_LineRest_244 a0 a1 = ()
data T_LineRest_244
  = C_lr'45'end_246 | C_lr'45'nl_250 |
    C_lr'45'char_258 T_LineRest_244
-- Once.Spec.Surface.Lexing.BlockRest
d_BlockRest_260 a0 a1 a2 = ()
data T_BlockRest_260
  = C_br'45'done_264 | C_br'45'end_268 | C_br'45'last_274 |
    C_br'45'open_282 T_BlockRest_260 |
    C_br'45'close_290 T_BlockRest_260 |
    C_br'45'char_302 T_BlockRest_260
-- Once.Spec.Surface.Lexing.Glyph
d_Glyph_304 a0 a1 a2 = ()
data T_Glyph_304
  = C_g'43'_308 | C_g'45'_312 | C_g'42'_316 | C_g'47'_320 |
    C_g'37'_324 | C_g'60'_328 | C_g'60''61'_332 | C_g'62'_336 |
    C_g'62''61'_340 | C_g'61''61'_344 | C_g'33''61'_348
-- Once.Spec.Surface.Lexing.Undotted
d_Undotted_350 a0 a1 = ()
data T_Undotted_350 = C_ud'45''37'_354 | C_ud_360
-- Once.Spec.Surface.Lexing.LexesChars
d_LexesChars_362 a0 a1 = ()
data T_LexesChars_362
  = C_lex'45'eof_364 | C_lex'45'space_370 T_LexesChars_362 |
    C_lex'45'tab_376 T_LexesChars_362 |
    C_lex'45'cr_382 T_LexesChars_362 |
    C_lex'45'nl'45'cont_390 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                            T_Next_140 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                            T_LexesChars_362 |
    C_lex'45'nl_396 T_LexesChars_362 |
    C_lex'45'caret1_402 T_LexesChars_362 |
    C_lex'45'caret0_408 T_LexesChars_362 |
    C_lex'45'caretw_414 T_LexesChars_362 |
    C_lex'45'comment_422 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                         T_LineRest_244 T_LexesChars_362 |
    C_lex'45'arrow_428 T_LexesChars_362 |
    C_lex'45'block_436 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       T_BlockRest_260 T_LexesChars_362 |
    C_lex'45'lbrace_442 T_LexesChars_362 |
    C_lex'45'op_452 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                    T_Glyph_304 T_Undotted_350 T_LexesChars_362 |
    C_lex'45'opd_462 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                     T_Glyph_304 T_LexesChars_362 |
    C_lex'45'equal_468 T_LexesChars_362 |
    C_lex'45'bang_474 T_LexesChars_362 |
    C_lex'45'lparen_480 T_LexesChars_362 |
    C_lex'45'rparen_486 T_LexesChars_362 |
    C_lex'45'rbrace_492 T_LexesChars_362 |
    C_lex'45'colon_498 T_LexesChars_362 |
    C_lex'45'lambda_504 T_LexesChars_362 |
    C_lex'45'comma_510 T_LexesChars_362 |
    C_lex'45'semi_516 T_LexesChars_362 |
    C_lex'45'at_522 T_LexesChars_362 |
    C_lex'45'pipe_528 T_LexesChars_362 |
    C_lex'45'amp_534 T_LexesChars_362 |
    C_lex'45'dot_540 T_LexesChars_362 |
    C_lex'45'string_550 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_StringBody_212
                        T_LexesChars_362 |
    C_lex'45'int_566 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                     [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_148
                     T_LexesChars_362 |
    C_lex'45'float_582 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_148
                       T_Fraction_168 T_LexesChars_362 |
    C_lex'45'ident_594 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_IdentRest_180
                       T_LexesChars_362
-- Once.Spec.Surface.Lexing.Lexes
d_Lexes_596 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> [T_Token_8] -> ()
d_Lexes_596 = erased
