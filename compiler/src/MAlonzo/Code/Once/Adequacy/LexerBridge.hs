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
d_LexesChars_6 a0 a1 = ()
data T_LexesChars_6
  = C_lex'45'eof_8 | C_lex'45'ws_16 T_LexesChars_6 |
    C_lex'45'nl'45'ind_24 T_LexesChars_6 |
    C_lex'45'nl_32 T_LexesChars_6 | C_lex'45'caret1_40 T_LexesChars_6 |
    C_lex'45'caret0_48 T_LexesChars_6 |
    C_lex'45'caretw_56 T_LexesChars_6 |
    C_lex'45'caret'45'gen_64 T_LexesChars_6 |
    C_lex'45'lcomment'45'ind_72 T_LexesChars_6 |
    C_lex'45'arrow'45'ind_80 T_LexesChars_6 |
    C_lex'45'minus_88 T_LexesChars_6 |
    C_lex'45'bcomment'45'ind_96 T_LexesChars_6 |
    C_lex'45'lbrace_104 T_LexesChars_6 |
    C_lex'45'le'45'ind_112 T_LexesChars_6 |
    C_lex'45'lt_120 T_LexesChars_6 |
    C_lex'45'ge'45'ind_128 T_LexesChars_6 |
    C_lex'45'gt_136 T_LexesChars_6 |
    C_lex'45'eqeq'45'ind_144 T_LexesChars_6 |
    C_lex'45'equals_152 T_LexesChars_6 |
    C_lex'45'neq'45'ind_160 T_LexesChars_6 |
    C_lex'45'bang_168 T_LexesChars_6 |
    C_lex'45'lparen_176 T_LexesChars_6 |
    C_lex'45'rparen_184 T_LexesChars_6 |
    C_lex'45'rbrace_192 T_LexesChars_6 |
    C_lex'45'colon_200 T_LexesChars_6 |
    C_lex'45'lambda_208 T_LexesChars_6 |
    C_lex'45'comma_216 T_LexesChars_6 |
    C_lex'45'semi_224 T_LexesChars_6 | C_lex'45'at_232 T_LexesChars_6 |
    C_lex'45'pipe_240 T_LexesChars_6 |
    C_lex'45'plus_248 T_LexesChars_6 |
    C_lex'45'star_256 T_LexesChars_6 |
    C_lex'45'slash_264 T_LexesChars_6 |
    C_lex'45'pct_272 T_LexesChars_6 | C_lex'45'amp_280 T_LexesChars_6 |
    C_lex'45'dot_288 T_LexesChars_6 |
    C_lex'45'string_302 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22 T_LexesChars_6 |
    C_lex'45'string'45'err_308 | C_lex'45'digit_316 T_LexesChars_6 |
    C_lex'45'float_330 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22 T_LexesChars_6 |
    C_lex'45'ident_338 T_LexesChars_6 |
    C_lex'45'skip_346 T_LexesChars_6
-- Once.Adequacy.LexerBridge.Lexes
d_Lexes_348 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Lexes_348 = erased
-- Once.Adequacy.LexerBridge.lexes-tok
d_lexes'45'tok_358 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> T_LexesChars_6
d_lexes'45'tok_358 v0 ~v1 = du_lexes'45'tok_358 v0
du_lexes'45'tok_358 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_LexesChars_6
du_lexes'45'tok_358 v0
  = case coe v0 of
      [] -> coe C_lex'45'eof_8
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe
                           eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
                           (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 ' '))
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                 (coe '\t')))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                 (coe '\r')))))
                     (coe MAlonzo.Code.Once.Parser.Lexer.C_hkWS_476)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                              (coe '\n')))
                        (coe MAlonzo.Code.Once.Parser.Lexer.C_hkNL_478)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                 (coe '^')))
                           (coe MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_480)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                    (coe '-')))
                              (coe MAlonzo.Code.Once.Parser.Lexer.C_hkDash_482)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                       (coe '{')))
                                 (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_484)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                          (coe '<')))
                                    (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLt_486)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v1) (coe '>')))
                                       (coe MAlonzo.Code.Once.Parser.Lexer.C_hkGt_488)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v1) (coe '=')))
                                          (coe MAlonzo.Code.Once.Parser.Lexer.C_hkEq_490)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v1) (coe '!')))
                                             (coe MAlonzo.Code.Once.Parser.Lexer.C_hkBang_492)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v1) (coe '(')))
                                                (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_494)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v1) (coe ')')))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_496)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v1) (coe '}')))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_498)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v1) (coe ':')))
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Lexer.C_hkColon_500)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v1) (coe '\\')))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_502)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v1) (coe ',')))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.C_hkComma_504)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v1) (coe ';')))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_506)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v1) (coe '@')))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.C_hkAt_508)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v1) (coe '|')))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_510)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v1)
                                                                                 (coe '+')))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_512)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v1)
                                                                                    (coe '*')))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Lexer.C_hkStar_514)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                       (coe v1)
                                                                                       (coe '/')))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_516)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                          (coe v1)
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
                                                                                                v1)
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
                                                                                                   v1)
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
                                                                                                      v1)
                                                                                                   (coe
                                                                                                      '"')))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_524)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_526))))))))))))))))))))))))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Lexer.C_hkWS_476
                  -> coe C_lex'45'ws_16 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkNL_478
                  -> coe
                       du_sound'45'nl_370 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_nlIndent_444 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_480
                  -> coe
                       du_sound'45'caret_382 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_caretClass_460 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDash_482
                  -> coe
                       du_sound'45'dash_394 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_dashClass_456 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_484
                  -> coe
                       du_sound'45'lbrace_406 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isDashHead_452 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLt_486
                  -> coe
                       du_sound'45'lt_418 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGt_488
                  -> coe
                       du_sound'45'gt_430 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkEq_490
                  -> coe
                       du_sound'45'eq_442 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkBang_492
                  -> coe
                       du_sound'45'bang_454 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_448 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_494
                  -> coe C_lex'45'lparen_176 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_496
                  -> coe C_lex'45'rparen_184 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_498
                  -> coe C_lex'45'rbrace_192 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkColon_500
                  -> coe C_lex'45'colon_200 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_502
                  -> coe C_lex'45'lambda_208 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkComma_504
                  -> coe C_lex'45'comma_216 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_506
                  -> coe C_lex'45'semi_224 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAt_508
                  -> coe C_lex'45'at_232 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_510
                  -> coe C_lex'45'pipe_240 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_512
                  -> coe C_lex'45'plus_248 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStar_514
                  -> coe C_lex'45'star_256 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_516
                  -> coe C_lex'45'slash_264 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPct_518
                  -> coe C_lex'45'pct_272 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_520
                  -> coe C_lex'45'amp_280 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDot_522
                  -> coe C_lex'45'dot_288 (coe du_lexes'45'tok_358 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_524
                  -> coe
                       du_sound'45'str_470
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_collectStringB_166 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_526
                  -> coe
                       du_sound'45'gen_502 (coe v2)
                       (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-nl
d_sound'45'nl_370 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'nl_370 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'nl_370 v1 v4
du_sound'45'nl_370 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'nl_370 v0 v1
  = if coe v1
      then coe C_lex'45'nl'45'ind_24 (coe du_lexes'45'tok_358 (coe v0))
      else coe C_lex'45'nl_32 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-caret
d_sound'45'caret_382 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_434 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'caret_382 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'caret_382 v1 v4
du_sound'45'caret_382 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_434 -> T_LexesChars_6
du_sound'45'caret_382 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'1_436
        -> coe
             C_lex'45'caret1_40
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'0_438
        -> coe
             C_lex'45'caret0_48
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'w_440
        -> coe
             C_lex'45'caretw_56
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'gen_442
        -> coe C_lex'45'caret'45'gen_64 (coe du_lexes'45'tok_358 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-dash
d_sound'45'dash_394 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_426 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'dash_394 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'dash_394 v1 v4
du_sound'45'dash_394 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_426 -> T_LexesChars_6
du_sound'45'dash_394 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'comment_428
        -> coe
             C_lex'45'lcomment'45'ind_72
             (coe
                du_lexes'45'tok_358
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_292
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'arrow_430
        -> coe
             C_lex'45'arrow'45'ind_80
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'minus_432
        -> coe C_lex'45'minus_88 (coe du_lexes'45'tok_358 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-lbrace
d_sound'45'lbrace_406 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lbrace_406 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'lbrace_406 v1 v4
du_sound'45'lbrace_406 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'lbrace_406 v0 v1
  = if coe v1
      then coe
             C_lex'45'bcomment'45'ind_96
             (coe
                du_lexes'45'tok_358
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_404
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))))
      else coe C_lex'45'lbrace_104 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-lt
d_sound'45'lt_418 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lt_418 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'lt_418 v1 v4
du_sound'45'lt_418 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'lt_418 v0 v1
  = if coe v1
      then coe
             C_lex'45'le'45'ind_112
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      else coe C_lex'45'lt_120 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-gt
d_sound'45'gt_430 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'gt_430 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'gt_430 v1 v4
du_sound'45'gt_430 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'gt_430 v0 v1
  = if coe v1
      then coe
             C_lex'45'ge'45'ind_128
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      else coe C_lex'45'gt_136 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-eq
d_sound'45'eq_442 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'eq_442 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'eq_442 v1 v4
du_sound'45'eq_442 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'eq_442 v0 v1
  = if coe v1
      then coe
             C_lex'45'eqeq'45'ind_144
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      else coe C_lex'45'equals_152 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-bang
d_sound'45'bang_454 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'bang_454 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'bang_454 v1 v4
du_sound'45'bang_454 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'bang_454 v0 v1
  = if coe v1
      then coe
             C_lex'45'neq'45'ind_160
             (coe
                du_lexes'45'tok_358
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_464 (coe v0)))
      else coe C_lex'45'bang_168 (coe du_lexes'45'tok_358 (coe v0))
-- Once.Adequacy.LexerBridge.sound-str
d_sound'45'str_470 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'str_470 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_sound'45'str_470 v4
du_sound'45'str_470 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_LexesChars_6
du_sound'45'str_470 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           C_lex'45'string_302 v2 v4 v5 (coe du_lexes'45'tok_358 (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_lex'45'string'45'err_308
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-num
d_sound'45'num_488 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'num_488 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_sound'45'num_488 v1 v6
du_sound'45'num_488 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_LexesChars_6
du_sound'45'num_488 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           C_lex'45'float_330 v3 v5 v6 (coe du_lexes'45'tok_358 (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_lex'45'digit_316
             (coe
                du_lexes'45'tok_358
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-gen
d_sound'45'gen_502 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'gen_502 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_sound'45'gen_502 v1 v4 v5
du_sound'45'gen_502 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Bool -> Bool -> T_LexesChars_6
du_sound'45'gen_502 v0 v1 v2
  = if coe v1
      then coe
             du_sound'45'num_488 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.Lexer.d_collectFracB_108
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0)))))
      else (if coe v2
              then coe
                     C_lex'45'ident_338
                     (coe
                        du_lexes'45'tok_358
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_44 (coe v0)))))
              else coe C_lex'45'skip_346 (coe du_lexes'45'tok_358 (coe v0)))
-- Once.Adequacy.LexerBridge.lexer-sound
d_lexer'45'sound_918 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_LexesChars_6
d_lexer'45'sound_918 v0
  = coe
      du_lexes'45'tok_358
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Adequacy.LexerBridge.tok-complete
d_tok'45'complete_928 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tok'45'complete_928 = erased
-- Once.Adequacy.LexerBridge.lexer-complete
d_lexer'45'complete_1618 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lexer'45'complete_1618 = erased
