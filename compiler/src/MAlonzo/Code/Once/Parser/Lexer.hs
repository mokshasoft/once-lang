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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
-- Once.Parser.Lexer.Bounded
d_Bounded_22 :: () -> Integer -> ()
d_Bounded_22 = erased
-- Once.Parser.Lexer.BoundedStrict
d_BoundedStrict_32 :: () -> Integer -> ()
d_BoundedStrict_32 = erased
-- Once.Parser.Lexer.collectIdentB
d_collectIdentB_44 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdentB_44 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
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
                             (coe d_collectIdentB_44 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_44 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_44 (coe v2)))))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (coe (\ v4 v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                                (coe (0 :: Integer)) (coe v0)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectIdent
d_collectIdent_68 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdent_68 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectIdentB_44 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectIdentB_44 (coe v0))))
-- Once.Parser.Lexer.collectDigitsB
d_collectDigitsB_78 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigitsB_78 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
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
                             (coe d_collectDigitsB_78 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_78 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_78 (coe v2)))))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (coe (\ v4 v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                                (coe (0 :: Integer)) (coe v0)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectDigits
d_collectDigits_102 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigits_102 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectDigitsB_78 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectDigitsB_78 (coe v0))))
-- Once.Parser.Lexer.digitsToNat
d_digitsToNat_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_110 = coe d_go_120 (coe (0 :: Integer))
-- Once.Parser.Lexer._.charToDigit
d_charToDigit_116 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_charToDigit_116 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_toNat_6 v0)
      (coe d_toNat_6 '0')
-- Once.Parser.Lexer._.go
d_go_120 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_go_120 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_go_120
             (coe
                addInt (coe d_charToDigit_116 (coe v2))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectStringB
d_collectStringB_136 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectStringB_136 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3
                 = let v3 = d_collectStringB_136 (coe v2) in
                   coe
                     (case coe v3 of
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                          -> case coe v4 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                 -> coe
                                      seq (coe v6)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                               (coe v5))
                                            (coe v6)))
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
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe
                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                      (let v4 = \ v4 -> addInt (coe (1 :: Integer)) (coe v4) in
                                       coe (coe (\ v5 -> v4)))
                                      (coe (0 :: Integer)) (coe v2))))))
                '\\'
                  -> case coe v2 of
                       (:) v4 v5
                         -> case coe v4 of
                              '"'
                                -> let v6 = d_collectStringB_136 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe '"') (coe v8))
                                                            (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              '\\'
                                -> let v6 = d_collectStringB_136 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe '\\') (coe v8))
                                                            (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              'n'
                                -> let v6 = d_collectStringB_136 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe '\n') (coe v8))
                                                            (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              'r'
                                -> let v6 = d_collectStringB_136 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe '\r') (coe v8))
                                                            (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              't'
                                -> let v6 = d_collectStringB_136 (coe v5) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe '\t') (coe v8))
                                                            (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectString
d_collectString_242 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectString_242 v0
  = let v1 = d_collectStringB_136 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Lexer.skipLineB
d_skipLineB_262 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipLineB_262 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (:) v1 v2
        -> let v3
                 = let v3
                         = coe
                             MAlonzo.Code.Agda.Builtin.Char.d_primCharEquality_32 v1 '\n' in
                   coe
                     (if coe v3
                        then coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                     (coe (\ v4 v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                                     (coe (0 :: Integer)) (coe v0)))
                        else coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe d_skipLineB_262 (coe v2)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_skipLineB_262 (coe v2)))) in
           coe
             (case coe v1 of
                '\n'
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n') (coe v2))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                          (coe
                             MAlonzo.Code.Data.List.Base.du_length_268
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n') (coe v2))))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.skipLine
d_skipLine_286 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipLine_286 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipLineB_262 (coe v0))
-- Once.Parser.Lexer.skipLine-length
d_skipLine'45'length_292 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipLine'45'length_292 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipLineB_262 (coe v0))
-- Once.Parser.Lexer.skipBlockB-WF
d_skipBlockB'45'WF_300 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB'45'WF_300 v0 v1 ~v2 = du_skipBlockB'45'WF_300 v0 v1
du_skipBlockB'45'WF_300 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_skipBlockB'45'WF_300 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                []
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                (:) v3 v4
                  -> case coe v4 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_skipBlockB'45'WF_300 (coe v0) (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe du_skipBlockB'45'WF_300 (coe v0) (coe v4)))
                       (:) v5 v6
                         -> let v7
                                  = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Char.d_primCharEquality_32 v3
                                         '{')
                                      (coe d__'61''61'c__16 (coe v5) (coe '-')) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Char.d_primCharEquality_32 v3
                                            '-')
                                         (coe d__'61''61'c__16 (coe v5) (coe '}')) in
                               coe
                                 (if coe v7
                                    then coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 du_skipBlockB'45'WF_300
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 du_skipBlockB'45'WF_300
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                    else (if coe v8
                                            then coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_300 (coe v2) (coe v6)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_300 (coe v2) (coe v6)))
                                            else coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_300 (coe v0) (coe v4)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_300 (coe v0)
                                                         (coe v4))))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Lexer.skipBlockB
d_skipBlockB_374 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB_374 v0 v1
  = coe du_skipBlockB'45'WF_300 (coe v0) (coe v1)
-- Once.Parser.Lexer.skipBlock
d_skipBlock_380 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipBlock_380 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipBlockB_374 (coe v0) (coe v1))
-- Once.Parser.Lexer.skipBlock-length
d_skipBlock'45'length_390 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipBlock'45'length_390 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipBlockB_374 (coe v0) (coe v1))
-- Once.Parser.Lexer.Dash3
d_Dash3_396 = ()
data T_Dash3_396
  = C_d'45'comment_398 | C_d'45'arrow_400 | C_d'45'minus_402
-- Once.Parser.Lexer.Caret4
d_Caret4_404 = ()
data T_Caret4_404
  = C_c'45'1_406 | C_c'45'0_408 | C_c'45'w_410 | C_c'45'gen_412
-- Once.Parser.Lexer.nlIndent
d_nlIndent_414 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_nlIndent_414 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe ' ')))
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '\t')))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.isEqHead
d_isEqHead_418 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isEqHead_418 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '='))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.isDashHead
d_isDashHead_422 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isDashHead_422 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '-'))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.dashClass
d_dashClass_426 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Dash3_396
d_dashClass_426 v0
  = case coe v0 of
      [] -> coe C_d'45'minus_402
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '-')))
             (coe C_d'45'comment_398)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '>')))
                (coe C_d'45'arrow_400) (coe C_d'45'minus_402))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.caretClass
d_caretClass_430 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Caret4_404
d_caretClass_430 v0
  = case coe v0 of
      [] -> coe C_c'45'gen_412
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '1')))
             (coe C_c'45'1_406)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '0')))
                (coe C_c'45'0_408)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                      (coe
                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                         (coe 'w')))
                   (coe C_c'45'w_410) (coe C_c'45'gen_412)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.drop1
d_drop1_434 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_drop1_434 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.drop1-≤
d_drop1'45''8804'_440 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop1'45''8804'_440 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268 (d_drop1_434 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.HeadK
d_HeadK_444 = ()
data T_HeadK_444
  = C_hkWS_446 | C_hkNL_448 | C_hkCaret_450 | C_hkDash_452 |
    C_hkLBrace_454 | C_hkLt_456 | C_hkGt_458 | C_hkEq_460 |
    C_hkBang_462 | C_hkLParen_464 | C_hkRParen_466 | C_hkRBrace_468 |
    C_hkColon_470 | C_hkLambda_472 | C_hkComma_474 | C_hkSemi_476 |
    C_hkAt_478 | C_hkPipe_480 | C_hkPlus_482 | C_hkStar_484 |
    C_hkSlash_486 | C_hkPct_488 | C_hkAmp_490 | C_hkDot_492 |
    C_hkStr_494 | C_hkGen_496
-- Once.Parser.Lexer.headK
d_headK_498 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> T_HeadK_444
d_headK_498 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
               (coe ' ')))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                  (coe '\t')))
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                  (coe '\r')))))
      (coe C_hkWS_446)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
               (coe '\n')))
         (coe C_hkNL_448)
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                  (coe '^')))
            (coe C_hkCaret_450)
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                  (coe
                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                     (coe '-')))
               (coe C_hkDash_452)
               (coe
                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                        (coe '{')))
                  (coe C_hkLBrace_454)
                  (coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe
                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                           (coe '<')))
                     (coe C_hkLt_456)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                              (coe '>')))
                        (coe C_hkGt_458)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                 (coe '=')))
                           (coe C_hkEq_460)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                    (coe '!')))
                              (coe C_hkBang_462)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                       (coe '(')))
                                 (coe C_hkLParen_464)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                          (coe ')')))
                                    (coe C_hkRParen_466)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v0) (coe '}')))
                                       (coe C_hkRBrace_468)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v0) (coe ':')))
                                          (coe C_hkColon_470)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v0) (coe '\\')))
                                             (coe C_hkLambda_472)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v0) (coe ',')))
                                                (coe C_hkComma_474)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v0) (coe ';')))
                                                   (coe C_hkSemi_476)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v0) (coe '@')))
                                                      (coe C_hkAt_478)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v0) (coe '|')))
                                                         (coe C_hkPipe_480)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v0) (coe '+')))
                                                            (coe C_hkPlus_482)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v0) (coe '*')))
                                                               (coe C_hkStar_484)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v0) (coe '/')))
                                                                  (coe C_hkSlash_486)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v0) (coe '%')))
                                                                     (coe C_hkPct_488)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v0) (coe '&')))
                                                                        (coe C_hkAmp_490)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v0)
                                                                                 (coe '.')))
                                                                           (coe C_hkDot_492)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v0)
                                                                                    (coe '"')))
                                                                              (coe C_hkStr_494)
                                                                              (coe
                                                                                 C_hkGen_496)))))))))))))))))))))))))
-- Once.Parser.Lexer.tok-str
d_tok'45'str_510 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'str_510 ~v0 ~v1 v2 = du_tok'45'str_510 v2
du_tok'45'str_510 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'str_510 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Parser.Token.C_TString_12
                              (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v2))
                           (coe du_tokenize'45'WF_560 (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-gen
d_tok'45'gen_518 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'gen_518 v0 v1 ~v2 v3 v4 = du_tok'45'gen_518 v0 v1 v3 v4
du_tok'45'gen_518 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'gen_518 v0 v1 v2 v3
  = if coe v2
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TInt_10
                (coe
                   d_digitsToNat_110
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe d_collectDigitsB_78 (coe v1))))))
             (coe
                du_tokenize'45'WF_560
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_collectDigitsB_78 (coe v1)))))
      else (if coe v3
              then coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Parser.Token.C_TWord_8
                        (coe
                           MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe d_collectIdentB_44 (coe v1))))))
                     (coe
                        du_tokenize'45'WF_560
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_collectIdentB_44 (coe v1)))))
              else coe du_tokenize'45'WF_560 (coe v1))
-- Once.Parser.Lexer.tok-nl
d_tok'45'nl_524 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'nl_524 v0 ~v1 v2 = du_tok'45'nl_524 v0 v2
du_tok'45'nl_524 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'nl_524 v0 v1
  = if coe v1
      then coe du_tokenize'45'WF_560 (coe v0)
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_72)
             (coe du_tokenize'45'WF_560 (coe v0))
-- Once.Parser.Lexer.tok-op2
d_tok'45'op2_530 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'op2_530 v0 ~v1 v2 v3 v4 = du_tok'45'op2_530 v0 v2 v3 v4
du_tok'45'op2_530 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'op2_530 v0 v1 v2 v3
  = if coe v3
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_tokenize'45'WF_560 (coe d_drop1_434 (coe v0)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du_tokenize'45'WF_560 (coe v0))
-- Once.Parser.Lexer.tok-lbrace
d_tok'45'lbrace_536 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'lbrace_536 v0 ~v1 v2 = du_tok'45'lbrace_536 v0 v2
du_tok'45'lbrace_536 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'lbrace_536 v0 v1
  = if coe v1
      then coe
             du_tokenize'45'WF_560
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_skipBlockB_374 (coe (1 :: Integer)) (coe d_drop1_434 (coe v0))))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_18)
             (coe du_tokenize'45'WF_560 (coe v0))
-- Once.Parser.Lexer.tok-minus
d_tok'45'minus_542 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Dash3_396 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'minus_542 v0 ~v1 v2 = du_tok'45'minus_542 v0 v2
du_tok'45'minus_542 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_Dash3_396 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'minus_542 v0 v1
  = case coe v1 of
      C_d'45'comment_398
        -> coe
             du_tokenize'45'WF_560
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_skipLineB_262 (coe d_drop1_434 (coe v0))))
      C_d'45'arrow_400
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_26)
             (coe du_tokenize'45'WF_560 (coe d_drop1_434 (coe v0)))
      C_d'45'minus_402
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_48)
             (coe du_tokenize'45'WF_560 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-caret
d_tok'45'caret_548 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Caret4_404 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'caret_548 v0 ~v1 v2 = du_tok'45'caret_548 v0 v2
du_tok'45'caret_548 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_Caret4_404 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'caret_548 v0 v1
  = case coe v1 of
      C_c'45'1_406
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_28)
             (coe du_tokenize'45'WF_560 (coe d_drop1_434 (coe v0)))
      C_c'45'0_408
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_30)
             (coe du_tokenize'45'WF_560 (coe d_drop1_434 (coe v0)))
      C_c'45'w_410
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_32)
             (coe du_tokenize'45'WF_560 (coe d_drop1_434 (coe v0)))
      C_c'45'gen_412
        -> coe
             du_tok'45'gen_518 (coe '^') (coe v0)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 '^')
             (coe d_isIdentStart_8 (coe '^'))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-head
d_tok'45'head_556 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_HeadK_444 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'head_556 v0 v1 ~v2 v3 = du_tok'45'head_556 v0 v1 v3
du_tok'45'head_556 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_HeadK_444 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'head_556 v0 v1 v2
  = case coe v2 of
      C_hkWS_446 -> coe du_tokenize'45'WF_560 (coe v1)
      C_hkNL_448
        -> coe du_tok'45'nl_524 (coe v1) (coe d_nlIndent_414 (coe v1))
      C_hkCaret_450
        -> coe du_tok'45'caret_548 (coe v1) (coe d_caretClass_430 (coe v1))
      C_hkDash_452
        -> coe du_tok'45'minus_542 (coe v1) (coe d_dashClass_426 (coe v1))
      C_hkLBrace_454
        -> coe
             du_tok'45'lbrace_536 (coe v1) (coe d_isDashHead_422 (coe v1))
      C_hkLt_456
        -> coe
             du_tok'45'op2_530 (coe v1)
             (coe MAlonzo.Code.Once.Parser.Token.C_TLe_60)
             (coe MAlonzo.Code.Once.Parser.Token.C_TLt_58)
             (coe d_isEqHead_418 (coe v1))
      C_hkGt_458
        -> coe
             du_tok'45'op2_530 (coe v1)
             (coe MAlonzo.Code.Once.Parser.Token.C_TGe_64)
             (coe MAlonzo.Code.Once.Parser.Token.C_TGt_62)
             (coe d_isEqHead_418 (coe v1))
      C_hkEq_460
        -> coe
             du_tok'45'op2_530 (coe v1)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_66)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_24)
             (coe d_isEqHead_418 (coe v1))
      C_hkBang_462
        -> coe
             du_tok'45'op2_530 (coe v1)
             (coe MAlonzo.Code.Once.Parser.Token.C_TNeq_68)
             (coe MAlonzo.Code.Once.Parser.Token.C_TBang_70)
             (coe d_isEqHead_418 (coe v1))
      C_hkLParen_464
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_14)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkRParen_466
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkRBrace_468
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRBrace_20)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkColon_470
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TColon_22)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkLambda_472
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_34)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkComma_474
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TComma_36)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkSemi_476
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_38)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkAt_478
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAt_40)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkPipe_480
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPipe_42)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkPlus_482
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_46)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkStar_484
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TStar_50)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkSlash_486
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_52)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkPct_488
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_54)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkAmp_490
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAmpersand_56)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkDot_492
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TDot_44)
             (coe du_tokenize'45'WF_560 (coe v1))
      C_hkStr_494
        -> coe du_tok'45'str_510 (coe d_collectStringB_136 (coe v1))
      C_hkGen_496
        -> coe
             du_tok'45'gen_518 (coe v0) (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
             (coe d_isIdentStart_8 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tokenize-WF
d_tokenize'45'WF_560 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize'45'WF_560 v0 ~v1 = du_tokenize'45'WF_560 v0
du_tokenize'45'WF_560 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tokenize'45'WF_560 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TEOF_74) (coe v0)
      (:) v1 v2
        -> coe
             du_tok'45'head_556 (coe v1) (coe v2) (coe d_headK_498 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tokenize
d_tokenize_828 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize_828 v0 = coe du_tokenize'45'WF_560 (coe v0)
-- Once.Parser.Lexer.tokenizeString
d_tokenizeString_832 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenizeString_832 v0
  = coe
      d_tokenize_828
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
