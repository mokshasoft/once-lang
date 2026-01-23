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

module MAlonzo.Code.Once.Parser.Lexer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Lexer.toNat
d_toNat_6 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_toNat_6 = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
-- Once.Parser.Lexer.isIdentStart
d_isIdentStart_8 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentStart_8 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '_'))
-- Once.Parser.Lexer.isIdentContinue
d_isIdentContinue_12 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isIdentContinue_12 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '_'))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '\''))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '+'))
                  (coe
                     MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                     (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '*'))
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '!'))
                        (coe eqInt (coe d_toNat_6 v0) (coe d_toNat_6 '?'))))))))
-- Once.Parser.Lexer._==c_
d__'61''61'c__16 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d__'61''61'c__16 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharEquality_32 v0 v1
-- Once.Parser.Lexer.collectIdent
d_collectIdent_22 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdent_22 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v0)
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                     (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v1)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                           (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '_'))
                           (coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '\''))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '+'))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                    (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '*'))
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                       (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '!'))
                                       (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '?')))))))) in
           coe
             (if coe v3
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_collectIdent_22 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_collectIdent_22 (coe v2)))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectDigits
d_collectDigits_44 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigits_44 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v0)
      (:) v1 v2
        -> let v3
                 = coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1 in
           coe
             (if coe v3
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_collectDigits_44 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_collectDigits_44 (coe v2)))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.digitsToNat
d_digitsToNat_66 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_66 = coe d_go_76 (coe (0 :: Integer))
-- Once.Parser.Lexer._.charToDigit
d_charToDigit_72 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_charToDigit_72 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_toNat_6 v0)
      (coe d_toNat_6 '0')
-- Once.Parser.Lexer._.go
d_go_76 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_go_76 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_go_76
             (coe
                addInt (coe d_charToDigit_72 (coe v2))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectString
d_collectString_86 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectString_86 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3
                 = let v3 = d_collectString_86 (coe v2) in
                   coe
                     (case coe v3 of
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                          -> case coe v4 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                 -> coe
                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                            (coe v5))
                                         (coe v6))
                               _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                        _ -> MAlonzo.RTE.mazUnreachableError) in
           coe
             (case coe v1 of
                '"'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2))
                '\\'
                  -> case coe v2 of
                       (:) v4 v5
                         -> case coe v4 of
                              '"'
                                -> let v6 = d_collectString_86 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe '"') (coe v8))
                                                         (coe v9))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              '\\'
                                -> let v6 = d_collectString_86 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe '\\') (coe v8))
                                                         (coe v9))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              'n'
                                -> let v6 = d_collectString_86 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe '\n') (coe v8))
                                                         (coe v9))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              'r'
                                -> let v6 = d_collectString_86 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe '\r') (coe v8))
                                                         (coe v9))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              't'
                                -> let v6 = d_collectString_86 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe '\t') (coe v8))
                                                         (coe v9))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.skipLine
d_skipLine_180 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipLine_180 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_skipLine_180 (coe v2) in
           coe
             (case coe v1 of
                '\n'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n') (coe v2)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.skipBlock
d_skipBlock_186 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipBlock_186 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe v1
                (:) v3 v4
                  -> let v5 = d_skipBlock_186 (coe v0) (coe v4) in
                     coe
                       (case coe v3 of
                          '-'
                            -> case coe v4 of
                                 (:) v6 v7
                                   -> case coe v6 of
                                        '}' -> coe d_skipBlock_186 (coe v2) (coe v7)
                                        _ -> coe v5
                                 _ -> coe v5
                          '{'
                            -> case coe v4 of
                                 (:) v6 v7
                                   -> case coe v6 of
                                        '-'
                                          -> coe
                                               d_skipBlock_186
                                               (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v7)
                                        _ -> coe v5
                                 _ -> coe v5
                          _ -> coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Lexer.tokenize
d_tokenize_202 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize_202 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TEOF_64) (coe v0)
      (:) v1 v2
        -> let v3
                 = let v3
                         = coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1 in
                   coe
                     (if coe v3
                        then coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.Parser.Token.C_TInt_10
                                  (coe
                                     d_digitsToNat_66
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe d_collectDigits_44 (coe v2))))))
                               (coe
                                  d_tokenize_202
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe d_collectDigits_44 (coe v2))))
                        else (let v4
                                    = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v1)
                                        (coe eqInt (coe d_toNat_6 v1) (coe d_toNat_6 '_')) in
                              coe
                                (if coe v4
                                   then coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.Parser.Token.C_TWord_8
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe v1)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe d_collectIdent_22 (coe v2))))))
                                          (coe
                                             d_tokenize_202
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe d_collectIdent_22 (coe v2))))
                                   else coe d_tokenize_202 (coe v2)))) in
           coe
             (case coe v1 of
                '\t' -> coe d_tokenize_202 (coe v2)
                '\n'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_62)
                       (coe d_tokenize_202 (coe v2))
                '\r' -> coe d_tokenize_202 (coe v2)
                ' ' -> coe d_tokenize_202 (coe v2)
                '!'
                  -> case coe v2 of
                       (:) v4 v5
                         -> case coe v4 of
                              '='
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe MAlonzo.Code.Once.Parser.Token.C_TNeq_60)
                                     (coe d_tokenize_202 (coe v5))
                              _ -> coe v3
                       _ -> coe v3
                '"'
                  -> let v4 = d_collectString_86 (coe v2) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.Parser.Token.C_TString_12
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                              v6))
                                        (coe d_tokenize_202 (coe v7))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                          _ -> MAlonzo.RTE.mazUnreachableError)
                '%'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_48)
                       (coe d_tokenize_202 (coe v2))
                '('
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
                       (coe d_tokenize_202 (coe v2))
                ')'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
                       (coe d_tokenize_202 (coe v2))
                '*'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TStar_44)
                       (coe d_tokenize_202 (coe v2))
                '+'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_40)
                       (coe d_tokenize_202 (coe v2))
                ','
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TComma_30)
                       (coe d_tokenize_202 (coe v2))
                '-'
                  -> let v4
                           = coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_42)
                               (coe d_tokenize_202 (coe v2)) in
                     coe
                       (case coe v2 of
                          (:) v5 v6
                            -> case coe v5 of
                                 '-' -> coe d_tokenize_202 (coe d_skipLine_180 (coe v6))
                                 '>'
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_26)
                                        (coe d_tokenize_202 (coe v6))
                                 _ -> coe v4
                          _ -> coe v4)
                '.'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TDot_38)
                       (coe d_tokenize_202 (coe v2))
                '/'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_46)
                       (coe d_tokenize_202 (coe v2))
                ':'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TColon_22)
                       (coe d_tokenize_202 (coe v2))
                ';'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_32)
                       (coe d_tokenize_202 (coe v2))
                '<'
                  -> let v4
                           = coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TLt_50)
                               (coe d_tokenize_202 (coe v2)) in
                     coe
                       (case coe v2 of
                          (:) v5 v6
                            -> case coe v5 of
                                 '='
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TLe_52)
                                        (coe d_tokenize_202 (coe v6))
                                 _ -> coe v4
                          _ -> coe v4)
                '='
                  -> let v4
                           = coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_24)
                               (coe d_tokenize_202 (coe v2)) in
                     coe
                       (case coe v2 of
                          (:) v5 v6
                            -> case coe v5 of
                                 '='
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_58)
                                        (coe d_tokenize_202 (coe v6))
                                 _ -> coe v4
                          _ -> coe v4)
                '>'
                  -> let v4
                           = coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TGt_54)
                               (coe d_tokenize_202 (coe v2)) in
                     coe
                       (case coe v2 of
                          (:) v5 v6
                            -> case coe v5 of
                                 '='
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe MAlonzo.Code.Once.Parser.Token.C_TGe_56)
                                        (coe d_tokenize_202 (coe v6))
                                 _ -> coe v4
                          _ -> coe v4)
                '@'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TAt_34)
                       (coe d_tokenize_202 (coe v2))
                '\\'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_28)
                       (coe d_tokenize_202 (coe v2))
                '{'
                  -> let v4
                           = coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_18)
                               (coe d_tokenize_202 (coe v2)) in
                     coe
                       (case coe v2 of
                          (:) v5 v6
                            -> case coe v5 of
                                 '-'
                                   -> coe
                                        d_tokenize_202
                                        (coe d_skipBlock_186 (coe (1 :: Integer)) (coe v6))
                                 _ -> coe v4
                          _ -> coe v4)
                '|'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TPipe_36)
                       (coe d_tokenize_202 (coe v2))
                '}'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Once.Parser.Token.C_TRBrace_20)
                       (coe d_tokenize_202 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tokenizeString
d_tokenizeString_316 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenizeString_316 v0
  = coe
      d_tokenize_202
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
