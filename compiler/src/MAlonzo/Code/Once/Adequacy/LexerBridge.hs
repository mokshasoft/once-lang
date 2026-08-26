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

module MAlonzo.Code.Once.Adequacy.LexerBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.LexerBridge.LexesChars
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
-- Once.Adequacy.LexerBridge.Lexes
d_Lexes_432 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Lexes_432 = erased
-- Once.Adequacy.LexerBridge.lexes-tok
d_lexes'45'tok_444 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> T_LexesChars_6
d_lexes'45'tok_444 v0 v1 ~v2 = du_lexes'45'tok_444 v0 v1
du_lexes'45'tok_444 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> T_LexesChars_6
du_lexes'45'tok_444 v0 v1
  = case coe v0 of
      [] -> coe C_lex'45'eof_10
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe
                           eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v2)
                           (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 ' '))
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                 (coe '\t')))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                 (coe '\r')))))
                     (coe MAlonzo.Code.Once.Parser.Lexer.C_hkWS_476)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                              (coe '\n')))
                        (coe MAlonzo.Code.Once.Parser.Lexer.C_hkNL_478)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                 (coe '^')))
                           (coe MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_480)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                    (coe '-')))
                              (coe MAlonzo.Code.Once.Parser.Lexer.C_hkDash_482)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                       (coe '{')))
                                 (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_484)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                          (coe '<')))
                                    (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLt_486)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v2) (coe '>')))
                                       (coe MAlonzo.Code.Once.Parser.Lexer.C_hkGt_488)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v2) (coe '=')))
                                          (coe MAlonzo.Code.Once.Parser.Lexer.C_hkEq_490)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v2) (coe '!')))
                                             (coe MAlonzo.Code.Once.Parser.Lexer.C_hkBang_492)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v2) (coe '(')))
                                                (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_494)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v2) (coe ')')))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_496)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v2) (coe '}')))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_498)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v2) (coe ':')))
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Lexer.C_hkColon_500)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v2) (coe '\\')))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_502)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v2) (coe ',')))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.C_hkComma_504)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v2) (coe ';')))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_506)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v2) (coe '@')))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.C_hkAt_508)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v2) (coe '|')))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_510)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v2)
                                                                                 (coe '+')))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_512)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v2)
                                                                                    (coe '*')))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Lexer.C_hkStar_514)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                       (coe v2)
                                                                                       (coe '/')))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_516)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             '%')))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Lexer.C_hkPct_518)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                       (coe
                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                             (coe
                                                                                                v2)
                                                                                             (coe
                                                                                                '&')))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_520)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                          (coe
                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   '.')))
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Parser.Lexer.C_hkDot_522)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                             (coe
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                                   (coe
                                                                                                      v2)
                                                                                                   (coe
                                                                                                      '"')))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_524)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_526))))))))))))))))))))))))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Parser.Lexer.C_hkWS_476
                  -> coe
                       C_lex'45'ws_20
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkNL_478
                  -> coe
                       du_sound'45'nl_458 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_nlIndent_444 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_480
                  -> coe
                       du_sound'45'caret_472 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_caretClass_460 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDash_482
                  -> coe
                       du_sound'45'dash_486 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_dashClass_456 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_484
                  -> coe
                       du_sound'45'lbrace_500 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isDashHead_452 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLt_486
                  -> coe
                       du_sound'45'lt_514 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGt_488
                  -> coe
                       du_sound'45'gt_528 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkEq_490
                  -> coe
                       du_sound'45'eq_542 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkBang_492
                  -> coe
                       du_sound'45'bang_556 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_494
                  -> coe
                       C_lex'45'lparen_220
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_496
                  -> coe
                       C_lex'45'rparen_230
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_498
                  -> coe
                       C_lex'45'rbrace_240
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkColon_500
                  -> coe
                       C_lex'45'colon_250
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_502
                  -> coe
                       C_lex'45'lambda_260
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkComma_504
                  -> coe
                       C_lex'45'comma_270
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_506
                  -> coe
                       C_lex'45'semi_280
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAt_508
                  -> coe
                       C_lex'45'at_290
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_510
                  -> coe
                       C_lex'45'pipe_300
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_512
                  -> coe
                       C_lex'45'plus_310
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStar_514
                  -> coe
                       C_lex'45'star_320
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_516
                  -> coe
                       C_lex'45'slash_330
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPct_518
                  -> coe
                       C_lex'45'pct_340
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_520
                  -> coe
                       C_lex'45'amp_350
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDot_522
                  -> coe
                       C_lex'45'dot_360
                       (coe
                          du_lexes'45'tok_444 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_524
                  -> coe
                       du_sound'45'str_574 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_collectStringB_166 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_526
                  -> coe
                       du_sound'45'gen_610 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-nl
d_sound'45'nl_458 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'nl_458 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'nl_458 v1 v2 v5
du_sound'45'nl_458 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'nl_458 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'nl'45'ind_30
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
      else coe
             C_lex'45'nl_40
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-caret
d_sound'45'caret_472 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_434 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'caret_472 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'caret_472 v1 v2 v5
du_sound'45'caret_472 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_434 -> T_LexesChars_6
du_sound'45'caret_472 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'1_436
        -> coe
             C_lex'45'caret1_50
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'0_438
        -> coe
             C_lex'45'caret0_60
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'w_440
        -> coe
             C_lex'45'caretw_70
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'gen_442
        -> coe
             C_lex'45'caret'45'gen_80
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-dash
d_sound'45'dash_486 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_426 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'dash_486 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'dash_486 v1 v2 v5
du_sound'45'dash_486 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_426 -> T_LexesChars_6
du_sound'45'dash_486 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'comment_428
        -> coe
             C_lex'45'lcomment'45'ind_90
             (coe
                du_lexes'45'tok_444
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_292
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_292
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'arrow_430
        -> coe
             C_lex'45'arrow'45'ind_100
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'minus_432
        -> coe
             C_lex'45'minus_110
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-lbrace
d_sound'45'lbrace_500 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lbrace_500 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'lbrace_500 v1 v2 v5
du_sound'45'lbrace_500 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'lbrace_500 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'bcomment'45'ind_120
             (coe
                du_lexes'45'tok_444
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_404
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_404
                         (coe (1 :: Integer))
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))))
                   (coe v1)))
      else coe
             C_lex'45'lbrace_130
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-lt
d_sound'45'lt_514 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lt_514 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'lt_514 v1 v2 v5
du_sound'45'lt_514 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'lt_514 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'le'45'ind_140
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      else coe
             C_lex'45'lt_150
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-gt
d_sound'45'gt_528 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'gt_528 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'gt_528 v1 v2 v5
du_sound'45'gt_528 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'gt_528 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'ge'45'ind_160
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      else coe
             C_lex'45'gt_170
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-eq
d_sound'45'eq_542 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'eq_542 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'eq_542 v1 v2 v5
du_sound'45'eq_542 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'eq_542 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'eqeq'45'ind_180
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      else coe
             C_lex'45'equals_190
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-bang
d_sound'45'bang_556 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'bang_556 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'bang_556 v1 v2 v5
du_sound'45'bang_556 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> T_LexesChars_6
du_sound'45'bang_556 v0 v1 v2
  = if coe v2
      then coe
             C_lex'45'neq'45'ind_200
             (coe
                du_lexes'45'tok_444
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0))
                   (coe v1)))
      else coe
             C_lex'45'bang_210
             (coe
                du_lexes'45'tok_444 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-str
d_sound'45'str_574 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'str_574 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'str_574 v1 v2 v5
du_sound'45'str_574 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_LexesChars_6
du_sound'45'str_574 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           C_lex'45'string_376 v4 v6 v7
                           (coe
                              du_lexes'45'tok_444 (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v6)
                                 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_lex'45'string'45'err_384
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-num
d_sound'45'num_594 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'num_594 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_sound'45'num_594 v1 v2 v7
du_sound'45'num_594 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_LexesChars_6
du_sound'45'num_594 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           C_lex'45'float_410 v4 v6 v7
                           (coe
                              du_lexes'45'tok_444 (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v6)
                                 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_lex'45'digit_394
             (coe
                du_lexes'45'tok_444
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0))))
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-gen
d_sound'45'gen_610 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'gen_610 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_sound'45'gen_610 v1 v2 v5 v6
du_sound'45'gen_610 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> Bool -> T_LexesChars_6
du_sound'45'gen_610 v0 v1 v2 v3
  = if coe v2
      then coe
             du_sound'45'num_594 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_collectFracB_108
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0)))))
      else (if coe v3
              then coe
                     C_lex'45'ident_420
                     (coe
                        du_lexes'45'tok_444
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_44 (coe v0))))
                        (coe
                           MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_44 (coe v0))))
                           (coe v1)))
              else coe
                     C_lex'45'skip_430
                     (coe
                        du_lexes'45'tok_444 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Lexer.d_adv_628 (coe v0) (coe v0)
                           (coe v1))))
-- Once.Adequacy.LexerBridge.lexer-sound
d_lexer'45'sound_1134 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_LexesChars_6
d_lexer'45'sound_1134 v0
  = coe
      du_lexes'45'tok_444
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe (0 :: Integer))
-- Once.Adequacy.LexerBridge.tok-complete
d_tok'45'complete_1146 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tok'45'complete_1146 = erased
-- Once.Adequacy.LexerBridge.lexer-complete
d_lexer'45'complete_1836 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lexer'45'complete_1836 = erased
