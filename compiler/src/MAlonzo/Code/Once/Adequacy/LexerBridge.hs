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
import qualified MAlonzo.Code.Once.Lang.Lexing
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.LexerBridge.lexes-tok
d_lexes'45'tok_12 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_lexes'45'tok_12 v0 v1 ~v2 = du_lexes'45'tok_12 v0 v1
du_lexes'45'tok_12 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_lexes'45'tok_12 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Lang.Lexing.C_lex'45'eof_10
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
                     (coe MAlonzo.Code.Once.Parser.Lexer.C_hkWS_460)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                              (coe '\n')))
                        (coe MAlonzo.Code.Once.Parser.Lexer.C_hkNL_462)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                 (coe '^')))
                           (coe MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_464)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                    (coe '-')))
                              (coe MAlonzo.Code.Once.Parser.Lexer.C_hkDash_466)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                       (coe '{')))
                                 (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_468)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                          (coe '<')))
                                    (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLt_470)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v2) (coe '>')))
                                       (coe MAlonzo.Code.Once.Parser.Lexer.C_hkGt_472)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v2) (coe '=')))
                                          (coe MAlonzo.Code.Once.Parser.Lexer.C_hkEq_474)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v2) (coe '!')))
                                             (coe MAlonzo.Code.Once.Parser.Lexer.C_hkBang_476)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v2) (coe '(')))
                                                (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_478)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v2) (coe ')')))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_480)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v2) (coe '}')))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_482)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v2) (coe ':')))
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Lexer.C_hkColon_484)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v2) (coe '\\')))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_486)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v2) (coe ',')))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.C_hkComma_488)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v2) (coe ';')))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_490)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v2) (coe '@')))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.C_hkAt_492)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v2) (coe '|')))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_494)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v2)
                                                                                 (coe '+')))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_496)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v2)
                                                                                    (coe '*')))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Lexer.C_hkStar_498)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                       (coe v2)
                                                                                       (coe '/')))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_500)
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
                                                                                       MAlonzo.Code.Once.Parser.Lexer.C_hkPct_502)
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
                                                                                          MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_504)
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
                                                                                             MAlonzo.Code.Once.Parser.Lexer.C_hkDot_506)
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
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_508)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_510))))))))))))))))))))))))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Parser.Lexer.C_hkWS_460
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'ws_20
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkNL_462
                  -> coe
                       du_sound'45'nl_26 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_nlIndent_428 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_464
                  -> coe
                       du_sound'45'caret_40 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_caretClass_444 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDash_466
                  -> coe
                       du_sound'45'dash_54 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_dashClass_440 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_468
                  -> coe
                       du_sound'45'lbrace_68 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isDashHead_436 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLt_470
                  -> coe
                       du_sound'45'lt_82 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGt_472
                  -> coe
                       du_sound'45'gt_96 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkEq_474
                  -> coe
                       du_sound'45'eq_110 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkBang_476
                  -> coe
                       du_sound'45'bang_124 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_432 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_478
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'lparen_220
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_480
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'rparen_230
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_482
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'rbrace_240
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkColon_484
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'colon_250
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_486
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'lambda_260
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkComma_488
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'comma_270
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_490
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'semi_280
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAt_492
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'at_290
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_494
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'pipe_300
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_496
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'plus_310
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStar_498
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'star_320
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_500
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'slash_330
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPct_502
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'pct_340
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_504
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'amp_350
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDot_506
                  -> coe
                       MAlonzo.Code.Once.Lang.Lexing.C_lex'45'dot_360
                       (coe
                          du_lexes'45'tok_12 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v3) (coe v3)
                             (coe v1)))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_508
                  -> coe
                       du_sound'45'str_142 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_collectStringB_168 (coe v3))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_510
                  -> coe
                       du_sound'45'gen_178 (coe v3) (coe v1)
                       (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v2))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-nl
d_sound'45'nl_26 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'nl_26 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'nl_26 v1 v2 v5
du_sound'45'nl_26 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'nl_26 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'nl'45'ind_30
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'nl_40
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-caret
d_sound'45'caret_40 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'caret_40 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'caret_40 v1 v2 v5
du_sound'45'caret_40 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_418 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'caret_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'1_420
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'caret1_50
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'0_422
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'caret0_60
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'w_424
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'caretw_70
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'gen_426
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'caret'45'gen_80
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-dash
d_sound'45'dash_54 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_410 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'dash_54 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'dash_54 v1 v2 v5
du_sound'45'dash_54 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_410 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'dash_54 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'comment_412
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'lcomment'45'ind_90
             (coe
                du_lexes'45'tok_12
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_274
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_274
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'arrow_414
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'arrow'45'ind_100
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'minus_416
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'minus_110
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-lbrace
d_sound'45'lbrace_68 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'lbrace_68 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'lbrace_68 v1 v2 v5
du_sound'45'lbrace_68 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'lbrace_68 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'bcomment'45'ind_120
             (coe
                du_lexes'45'tok_12
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_388
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_388
                         (coe (1 :: Integer))
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))))
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'lbrace_130
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-lt
d_sound'45'lt_82 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'lt_82 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'lt_82 v1 v2 v5
du_sound'45'lt_82 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'lt_82 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'le'45'ind_140
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'lt_150
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-gt
d_sound'45'gt_96 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'gt_96 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'gt_96 v1 v2 v5
du_sound'45'gt_96 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'gt_96 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'ge'45'ind_160
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'gt_170
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-eq
d_sound'45'eq_110 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'eq_110 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'eq_110 v1 v2 v5
du_sound'45'eq_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'eq_110 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'eqeq'45'ind_180
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'equals_190
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-bang
d_sound'45'bang_124 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'bang_124 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'bang_124 v1 v2 v5
du_sound'45'bang_124 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'bang_124 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'neq'45'ind_200
             (coe
                du_lexes'45'tok_12
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_448 (coe v0))
                   (coe v1)))
      else coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'bang_210
             (coe
                du_lexes'45'tok_12 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                   (coe v1)))
-- Once.Adequacy.LexerBridge.sound-str
d_sound'45'str_142 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'str_142 ~v0 v1 v2 ~v3 ~v4 v5 ~v6
  = du_sound'45'str_142 v1 v2 v5
du_sound'45'str_142 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'str_142 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Once.Lang.Lexing.C_lex'45'string_376 v4 v6 v7
                           (coe
                              du_lexes'45'tok_12 (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v6)
                                 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Lang.Lexing.C_lex'45'string'45'err_384
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-num
d_sound'45'num_162 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'num_162 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_sound'45'num_162 v1 v2 v7
du_sound'45'num_162 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'num_162 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Once.Lang.Lexing.C_lex'45'float_410 v4 v6 v7
                           (coe
                              du_lexes'45'tok_12 (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v6)
                                 (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Lang.Lexing.C_lex'45'digit_394
             (coe
                du_lexes'45'tok_12
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v0))))
                (coe
                   MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v0))))
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-gen
d_sound'45'gen_178 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_sound'45'gen_178 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_sound'45'gen_178 v1 v2 v5 v6
du_sound'45'gen_178 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Bool -> Bool -> MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
du_sound'45'gen_178 v0 v1 v2 v3
  = if coe v2
      then coe
             du_sound'45'num_162 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_collectFracB_110
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_80 (coe v0)))))
      else (if coe v3
              then coe
                     MAlonzo.Code.Once.Lang.Lexing.C_lex'45'ident_420
                     (coe
                        du_lexes'45'tok_12
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_46 (coe v0))))
                        (coe
                           MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_46 (coe v0))))
                           (coe v1)))
              else coe
                     MAlonzo.Code.Once.Lang.Lexing.C_lex'45'skip_430
                     (coe
                        du_lexes'45'tok_12 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Parser.Lexer.d_adv_612 (coe v0) (coe v0)
                           (coe v1))))
-- Once.Adequacy.LexerBridge.lexer-sound
d_lexer'45'sound_702 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6
d_lexer'45'sound_702 v0
  = coe
      du_lexes'45'tok_12
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe (0 :: Integer))
-- Once.Adequacy.LexerBridge.tok-step
d_tok'45'step_726 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6 ->
  ([MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tok'45'step_726 = erased
-- Once.Adequacy.LexerBridge.tok-complete
d_tok'45'complete_1506 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tok'45'complete_1506 = erased
-- Once.Adequacy.LexerBridge.lexer-complete
d_lexer'45'complete_1520 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Lang.Lexing.T_LexesChars_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lexer'45'complete_1520 = erased
