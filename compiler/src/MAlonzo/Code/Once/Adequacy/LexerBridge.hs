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
    C_lex'45'ident_324 T_LexesChars_6 |
    C_lex'45'skip_332 T_LexesChars_6
-- Once.Adequacy.LexerBridge.Lexes
d_Lexes_334 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_Lexes_334 = erased
-- Once.Adequacy.LexerBridge.lexes-tok
d_lexes'45'tok_344 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> T_LexesChars_6
d_lexes'45'tok_344 v0 ~v1 = du_lexes'45'tok_344 v0
du_lexes'45'tok_344 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_LexesChars_6
du_lexes'45'tok_344 v0
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
                     (coe MAlonzo.Code.Once.Parser.Lexer.C_hkWS_446)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                              (coe '\n')))
                        (coe MAlonzo.Code.Once.Parser.Lexer.C_hkNL_448)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                 (coe '^')))
                           (coe MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_450)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                    (coe '-')))
                              (coe MAlonzo.Code.Once.Parser.Lexer.C_hkDash_452)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                       (coe '{')))
                                 (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_454)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                                          (coe '<')))
                                    (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLt_456)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v1) (coe '>')))
                                       (coe MAlonzo.Code.Once.Parser.Lexer.C_hkGt_458)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v1) (coe '=')))
                                          (coe MAlonzo.Code.Once.Parser.Lexer.C_hkEq_460)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v1) (coe '!')))
                                             (coe MAlonzo.Code.Once.Parser.Lexer.C_hkBang_462)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v1) (coe '(')))
                                                (coe MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_464)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v1) (coe ')')))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_466)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v1) (coe '}')))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_468)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v1) (coe ':')))
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Lexer.C_hkColon_470)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v1) (coe '\\')))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_472)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v1) (coe ',')))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.C_hkComma_474)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v1) (coe ';')))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_476)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v1) (coe '@')))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.C_hkAt_478)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v1) (coe '|')))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_480)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v1)
                                                                                 (coe '+')))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_482)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v1)
                                                                                    (coe '*')))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Parser.Lexer.C_hkStar_484)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                       (coe v1)
                                                                                       (coe '/')))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_486)
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
                                                                                       MAlonzo.Code.Once.Parser.Lexer.C_hkPct_488)
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
                                                                                          MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_490)
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
                                                                                             MAlonzo.Code.Once.Parser.Lexer.C_hkDot_492)
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
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_494)
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_496))))))))))))))))))))))))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Lexer.C_hkWS_446
                  -> coe C_lex'45'ws_16 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkNL_448
                  -> coe
                       du_sound'45'nl_356 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_nlIndent_414 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkCaret_450
                  -> coe
                       du_sound'45'caret_368 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_caretClass_430 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDash_452
                  -> coe
                       du_sound'45'dash_380 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_dashClass_426 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLBrace_454
                  -> coe
                       du_sound'45'lbrace_392 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isDashHead_422 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLt_456
                  -> coe
                       du_sound'45'lt_404 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_418 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGt_458
                  -> coe
                       du_sound'45'gt_416 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_418 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkEq_460
                  -> coe
                       du_sound'45'eq_428 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_418 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkBang_462
                  -> coe
                       du_sound'45'bang_440 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isEqHead_418 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLParen_464
                  -> coe C_lex'45'lparen_176 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRParen_466
                  -> coe C_lex'45'rparen_184 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkRBrace_468
                  -> coe C_lex'45'rbrace_192 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkColon_470
                  -> coe C_lex'45'colon_200 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkLambda_472
                  -> coe C_lex'45'lambda_208 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkComma_474
                  -> coe C_lex'45'comma_216 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSemi_476
                  -> coe C_lex'45'semi_224 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAt_478
                  -> coe C_lex'45'at_232 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPipe_480
                  -> coe C_lex'45'pipe_240 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPlus_482
                  -> coe C_lex'45'plus_248 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStar_484
                  -> coe C_lex'45'star_256 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkSlash_486
                  -> coe C_lex'45'slash_264 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkPct_488
                  -> coe C_lex'45'pct_272 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkAmp_490
                  -> coe C_lex'45'amp_280 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkDot_492
                  -> coe C_lex'45'dot_288 (coe du_lexes'45'tok_344 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkStr_494
                  -> coe
                       du_sound'45'str_456
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_collectStringB_136 (coe v2))
                MAlonzo.Code.Once.Parser.Lexer.C_hkGen_496
                  -> coe
                       du_sound'45'gen_470 (coe v2)
                       (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-nl
d_sound'45'nl_356 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'nl_356 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'nl_356 v1 v4
du_sound'45'nl_356 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'nl_356 v0 v1
  = if coe v1
      then coe C_lex'45'nl'45'ind_24 (coe du_lexes'45'tok_344 (coe v0))
      else coe C_lex'45'nl_32 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-caret
d_sound'45'caret_368 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_404 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'caret_368 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'caret_368 v1 v4
du_sound'45'caret_368 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Lexer.T_Caret4_404 -> T_LexesChars_6
du_sound'45'caret_368 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'1_406
        -> coe
             C_lex'45'caret1_40
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'0_408
        -> coe
             C_lex'45'caret0_48
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'w_410
        -> coe
             C_lex'45'caretw_56
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_c'45'gen_412
        -> coe C_lex'45'caret'45'gen_64 (coe du_lexes'45'tok_344 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-dash
d_sound'45'dash_380 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'dash_380 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'dash_380 v1 v4
du_sound'45'dash_380 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Lexer.T_Dash3_396 -> T_LexesChars_6
du_sound'45'dash_380 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'comment_398
        -> coe
             C_lex'45'lcomment'45'ind_72
             (coe
                du_lexes'45'tok_344
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipLineB_262
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'arrow_400
        -> coe
             C_lex'45'arrow'45'ind_80
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      MAlonzo.Code.Once.Parser.Lexer.C_d'45'minus_402
        -> coe C_lex'45'minus_88 (coe du_lexes'45'tok_344 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-lbrace
d_sound'45'lbrace_392 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lbrace_392 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'lbrace_392 v1 v4
du_sound'45'lbrace_392 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'lbrace_392 v0 v1
  = if coe v1
      then coe
             C_lex'45'bcomment'45'ind_96
             (coe
                du_lexes'45'tok_344
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Parser.Lexer.d_skipBlockB_374
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))))
      else coe C_lex'45'lbrace_104 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-lt
d_sound'45'lt_404 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'lt_404 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'lt_404 v1 v4
du_sound'45'lt_404 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'lt_404 v0 v1
  = if coe v1
      then coe
             C_lex'45'le'45'ind_112
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      else coe C_lex'45'lt_120 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-gt
d_sound'45'gt_416 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'gt_416 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'gt_416 v1 v4
du_sound'45'gt_416 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'gt_416 v0 v1
  = if coe v1
      then coe
             C_lex'45'ge'45'ind_128
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      else coe C_lex'45'gt_136 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-eq
d_sound'45'eq_428 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'eq_428 ~v0 v1 ~v2 ~v3 v4 ~v5 = du_sound'45'eq_428 v1 v4
du_sound'45'eq_428 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'eq_428 v0 v1
  = if coe v1
      then coe
             C_lex'45'eqeq'45'ind_144
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      else coe C_lex'45'equals_152 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-bang
d_sound'45'bang_440 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'bang_440 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_sound'45'bang_440 v1 v4
du_sound'45'bang_440 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool -> T_LexesChars_6
du_sound'45'bang_440 v0 v1
  = if coe v1
      then coe
             C_lex'45'neq'45'ind_160
             (coe
                du_lexes'45'tok_344
                (coe MAlonzo.Code.Once.Parser.Lexer.d_drop1_434 (coe v0)))
      else coe C_lex'45'bang_168 (coe du_lexes'45'tok_344 (coe v0))
-- Once.Adequacy.LexerBridge.sound-str
d_sound'45'str_456 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_LexesChars_6
d_sound'45'str_456 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_sound'45'str_456 v4
du_sound'45'str_456 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_LexesChars_6
du_sound'45'str_456 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           C_lex'45'string_302 v2 v4 v5 (coe du_lexes'45'tok_344 (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_lex'45'string'45'err_308
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LexerBridge.sound-gen
d_sound'45'gen_470 ::
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
d_sound'45'gen_470 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_sound'45'gen_470 v1 v4 v5
du_sound'45'gen_470 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Bool -> Bool -> T_LexesChars_6
du_sound'45'gen_470 v0 v1 v2
  = if coe v1
      then coe
             C_lex'45'digit_316
             (coe
                du_lexes'45'tok_344
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_collectDigitsB_78 (coe v0)))))
      else (if coe v2
              then coe
                     C_lex'45'ident_324
                     (coe
                        du_lexes'45'tok_344
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe MAlonzo.Code.Once.Parser.Lexer.d_collectIdentB_44 (coe v0)))))
              else coe C_lex'45'skip_332 (coe du_lexes'45'tok_344 (coe v0)))
-- Once.Adequacy.LexerBridge.lexer-sound
d_lexer'45'sound_848 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_LexesChars_6
d_lexer'45'sound_848 v0
  = coe
      du_lexes'45'tok_344
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Adequacy.LexerBridge.tok-complete
d_tok'45'complete_858 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tok'45'complete_858 = erased
-- Once.Adequacy.LexerBridge.lexer-complete
d_lexer'45'complete_1514 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_LexesChars_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lexer'45'complete_1514 = erased
