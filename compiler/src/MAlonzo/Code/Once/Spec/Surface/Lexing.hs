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
-- Once.Spec.Surface.Lexing.digitsFrom
d_digitsFrom_90 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsFrom_90 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_digitsFrom_90
             (coe
                addInt
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_code_80 v2)
                   (coe d_code_80 '0'))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Lexing.digitsToNat
d_digitsToNat_100 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_100 = coe d_digitsFrom_90 (coe (0 :: Integer))
-- Once.Spec.Surface.Lexing.Special
d_Special_102 a0 = ()
data T_Special_102
  = C_sp'45'space_104 | C_sp'45'tab_106 | C_sp'45'cr_108 |
    C_sp'45'nl_110 | C_sp'45'backslash_112 | C_sp'45'caret_114 |
    C_sp'45'dash_116 | C_sp'45'lbrace_118 | C_sp'45'lt_120 |
    C_sp'45'gt_122 | C_sp'45'eq_124 | C_sp'45'bang_126 |
    C_sp'45'lparen_128 | C_sp'45'rparen_130 | C_sp'45'rbrace_132 |
    C_sp'45'colon_134 | C_sp'45'comma_136 | C_sp'45'semi_138 |
    C_sp'45'at_140 | C_sp'45'pipe_142 | C_sp'45'plus_144 |
    C_sp'45'star_146 | C_sp'45'slash_148 | C_sp'45'pct_150 |
    C_sp'45'amp_152 | C_sp'45'dot_154 | C_sp'45'quote_156
-- Once.Spec.Surface.Lexing.Next
d_Next_158 a0 a1 = ()
data T_Next_158 = C_next_164
-- Once.Spec.Surface.Lexing.Digits
d_Digits_166 a0 a1 a2 = ()
data T_Digits_166
  = C_dg'45'end_168 | C_dg'45'stop_174 |
    C_dg'45'more_184 T_Digits_166
-- Once.Spec.Surface.Lexing.Fraction
d_Fraction_186 a0 a1 a2 = ()
newtype T_Fraction_186 = C_fraction_196 T_Digits_166
-- Once.Spec.Surface.Lexing.IdentRest
d_IdentRest_198 a0 a1 a2 = ()
data T_IdentRest_198
  = C_id'45'end_200 | C_id'45'stop_206 |
    C_id'45'more_216 T_IdentRest_198
-- Once.Spec.Surface.Lexing.Escape
d_Escape_218 a0 a1 = ()
data T_Escape_218
  = C_esc'45'n_220 | C_esc'45't_222 | C_esc'45'r_224 |
    C_esc'45'bs_226 | C_esc'45'q_228
-- Once.Spec.Surface.Lexing.StringBody
d_StringBody_230 a0 a1 a2 = ()
data T_StringBody_230
  = C_sb'45'close_234 |
    C_sb'45'esc_246 T_Escape_218 T_StringBody_230 |
    C_sb'45'char_260 T_StringBody_230
-- Once.Spec.Surface.Lexing.LineRest
d_LineRest_262 a0 a1 = ()
data T_LineRest_262
  = C_lr'45'end_264 | C_lr'45'nl_268 |
    C_lr'45'char_276 T_LineRest_262
-- Once.Spec.Surface.Lexing.BlockRest
d_BlockRest_278 a0 a1 a2 = ()
data T_BlockRest_278
  = C_br'45'done_282 | C_br'45'end_286 | C_br'45'last_292 |
    C_br'45'open_300 T_BlockRest_278 |
    C_br'45'close_308 T_BlockRest_278 |
    C_br'45'char_320 T_BlockRest_278
-- Once.Spec.Surface.Lexing.LexesChars
d_LexesChars_322 a0 a1 = ()
data T_LexesChars_322
  = C_lex'45'eof_324 | C_lex'45'space_330 T_LexesChars_322 |
    C_lex'45'tab_336 T_LexesChars_322 |
    C_lex'45'cr_342 T_LexesChars_322 |
    C_lex'45'nl'45'cont_350 MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                            T_Next_158 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                            T_LexesChars_322 |
    C_lex'45'nl_356 T_LexesChars_322 |
    C_lex'45'caret1_362 T_LexesChars_322 |
    C_lex'45'caret0_368 T_LexesChars_322 |
    C_lex'45'caretw_374 T_LexesChars_322 |
    C_lex'45'comment_382 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                         T_LineRest_262 T_LexesChars_322 |
    C_lex'45'arrow_388 T_LexesChars_322 |
    C_lex'45'minus_394 T_LexesChars_322 |
    C_lex'45'block_402 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       T_BlockRest_278 T_LexesChars_322 |
    C_lex'45'lbrace_408 T_LexesChars_322 |
    C_lex'45'le_414 T_LexesChars_322 |
    C_lex'45'lt_420 T_LexesChars_322 |
    C_lex'45'ge_426 T_LexesChars_322 |
    C_lex'45'gt_432 T_LexesChars_322 |
    C_lex'45'eqeq_438 T_LexesChars_322 |
    C_lex'45'equal_444 T_LexesChars_322 |
    C_lex'45'neq_450 T_LexesChars_322 |
    C_lex'45'bang_456 T_LexesChars_322 |
    C_lex'45'lparen_462 T_LexesChars_322 |
    C_lex'45'rparen_468 T_LexesChars_322 |
    C_lex'45'rbrace_474 T_LexesChars_322 |
    C_lex'45'colon_480 T_LexesChars_322 |
    C_lex'45'lambda_486 T_LexesChars_322 |
    C_lex'45'comma_492 T_LexesChars_322 |
    C_lex'45'semi_498 T_LexesChars_322 |
    C_lex'45'at_504 T_LexesChars_322 |
    C_lex'45'pipe_510 T_LexesChars_322 |
    C_lex'45'plus_516 T_LexesChars_322 |
    C_lex'45'star_522 T_LexesChars_322 |
    C_lex'45'slash_528 T_LexesChars_322 |
    C_lex'45'pct_534 T_LexesChars_322 |
    C_lex'45'amp_540 T_LexesChars_322 |
    C_lex'45'dot_546 T_LexesChars_322 |
    C_lex'45'string_556 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_StringBody_230
                        T_LexesChars_322 |
    C_lex'45'int_572 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                     [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_166
                     T_LexesChars_322 |
    C_lex'45'float_588 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_Digits_166
                       T_Fraction_186 T_LexesChars_322 |
    C_lex'45'ident_600 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] T_IdentRest_198
                       T_LexesChars_322
-- Once.Spec.Surface.Lexing.Lexes
d_Lexes_602 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> [T_Token_8] -> ()
d_Lexes_602 = erased
