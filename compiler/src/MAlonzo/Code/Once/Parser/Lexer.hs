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
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
-- Once.Parser.Lexer.Bounded
d_Bounded_16 :: () -> Integer -> ()
d_Bounded_16 = erased
-- Once.Parser.Lexer.BoundedStrict
d_BoundedStrict_26 :: () -> Integer -> ()
d_BoundedStrict_26 = erased
-- Once.Parser.Lexer.collectIdentB
d_collectIdentB_38 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdentB_38 v0
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
                             (coe d_collectIdentB_38 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_38 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_38 (coe v2)))))
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
d_collectIdent_62 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdent_62 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectIdentB_38 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectIdentB_38 (coe v0))))
-- Once.Parser.Lexer.collectDigitsB
d_collectDigitsB_72 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigitsB_72 v0
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
                             (coe d_collectDigitsB_72 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_72 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_72 (coe v2)))))
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
-- Once.Parser.Lexer.collectFracB
d_collectFracB_102 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectFracB_102 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                '.'
                  -> case coe v3 of
                       (:) v4 v5
                         -> let v6
                                  = coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v4 in
                            coe
                              (if coe v6
                                 then coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe d_collectDigitsB_72 (coe v5))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe d_collectDigitsB_72 (coe v5))))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe d_collectDigitsB_72 (coe v5)))))))
                                 else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Lexer.collectDigits
d_collectDigits_126 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigits_126 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectDigitsB_72 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectDigitsB_72 (coe v0))))
-- Once.Parser.Lexer.digitsToNat
d_digitsToNat_134 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_134 = coe d_go_144 (coe (0 :: Integer))
-- Once.Parser.Lexer._.charToDigit
d_charToDigit_140 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_charToDigit_140 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe d_toNat_6 v0)
      (coe d_toNat_6 '0')
-- Once.Parser.Lexer._.go
d_go_144 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_go_144 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             d_go_144
             (coe
                addInt (coe d_charToDigit_140 (coe v2))
                (coe mulInt (coe v0) (coe (10 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectStringB
d_collectStringB_160 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectStringB_160 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3
                 = let v3 = d_collectStringB_160 (coe v2) in
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
                                -> let v6 = d_collectStringB_160 (coe v5) in
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
                                -> let v6 = d_collectStringB_160 (coe v5) in
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
                                -> let v6 = d_collectStringB_160 (coe v5) in
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
                                -> let v6 = d_collectStringB_160 (coe v5) in
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
                                -> let v6 = d_collectStringB_160 (coe v5) in
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
d_collectString_266 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectString_266 v0
  = let v1 = d_collectStringB_160 (coe v0) in
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
d_skipLineB_286 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipLineB_286 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (:) v1 v2
        -> let v3
                 = let v3
                         = coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                             (coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                erased erased
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v3 ->
                                      coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                        (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1))
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                      (coe
                                         eqInt
                                         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '\n'))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                         (coe
                                            eqInt
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                               '\n')))))) in
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
                                  (coe d_skipLineB_286 (coe v2)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_skipLineB_286 (coe v2)))) in
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
d_skipLine_310 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipLine_310 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipLineB_286 (coe v0))
-- Once.Parser.Lexer.skipLine-length
d_skipLine'45'length_316 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipLine'45'length_316 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipLineB_286 (coe v0))
-- Once.Parser.Lexer.skipBlockB-WF
d_skipBlockB'45'WF_324 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB'45'WF_324 v0 v1 ~v2 = du_skipBlockB'45'WF_324 v0 v1
du_skipBlockB'45'WF_324 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_skipBlockB'45'WF_324 v0 v1
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
                                 (coe du_skipBlockB'45'WF_324 (coe v0) (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe du_skipBlockB'45'WF_324 (coe v0) (coe v4)))
                       (:) v5 v6
                         -> let v7
                                  = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                            erased erased
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                               erased
                                               (\ v7 ->
                                                  coe
                                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                       v3))
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe
                                                     eqInt
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                        v3)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                        '{'))
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                     (coe
                                                        eqInt
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                           v3)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                           '{')))))))
                                      (coe
                                         MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v5)
                                         (coe '-')) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                               erased erased
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                  erased
                                                  (\ v8 ->
                                                     coe
                                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                          v3))
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe
                                                        eqInt
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                           v3)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                           '-'))
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                        (coe
                                                           eqInt
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                              v3)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                              '-')))))))
                                         (coe
                                            MAlonzo.Code.Data.Char.Properties.d__'61''61'__26
                                            (coe v5) (coe '}')) in
                               coe
                                 (if coe v7
                                    then coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 du_skipBlockB'45'WF_324
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 du_skipBlockB'45'WF_324
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                    else (if coe v8
                                            then coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_324 (coe v2) (coe v6)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_324 (coe v2) (coe v6)))
                                            else coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_324 (coe v0) (coe v4)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_324 (coe v0)
                                                         (coe v4))))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Lexer.skipBlockB
d_skipBlockB_398 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB_398 v0 v1
  = coe du_skipBlockB'45'WF_324 (coe v0) (coe v1)
-- Once.Parser.Lexer.skipBlock
d_skipBlock_404 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipBlock_404 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipBlockB_398 (coe v0) (coe v1))
-- Once.Parser.Lexer.skipBlock-length
d_skipBlock'45'length_414 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipBlock'45'length_414 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipBlockB_398 (coe v0) (coe v1))
-- Once.Parser.Lexer.Dash3
d_Dash3_420 = ()
data T_Dash3_420
  = C_d'45'comment_422 | C_d'45'arrow_424 | C_d'45'minus_426
-- Once.Parser.Lexer.Caret4
d_Caret4_428 = ()
data T_Caret4_428
  = C_c'45'1_430 | C_c'45'0_432 | C_c'45'w_434 | C_c'45'gen_436
-- Once.Parser.Lexer.nlIndent
d_nlIndent_438 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_nlIndent_438 v0
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
d_isEqHead_442 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isEqHead_442 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '='))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.isDashHead
d_isDashHead_446 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isDashHead_446 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '-'))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.dashClass
d_dashClass_450 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Dash3_420
d_dashClass_450 v0
  = case coe v0 of
      [] -> coe C_d'45'minus_426
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '-')))
             (coe C_d'45'comment_422)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '>')))
                (coe C_d'45'arrow_424) (coe C_d'45'minus_426))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.caretClass
d_caretClass_454 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Caret4_428
d_caretClass_454 v0
  = case coe v0 of
      [] -> coe C_c'45'gen_436
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '1')))
             (coe C_c'45'1_430)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '0')))
                (coe C_c'45'0_432)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                      (coe
                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                         (coe 'w')))
                   (coe C_c'45'w_434) (coe C_c'45'gen_436)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.drop1
d_drop1_458 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_drop1_458 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.drop1-≤
d_drop1'45''8804'_464 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop1'45''8804'_464 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268 (d_drop1_458 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.HeadK
d_HeadK_468 = ()
data T_HeadK_468
  = C_hkWS_470 | C_hkNL_472 | C_hkCaret_474 | C_hkDash_476 |
    C_hkLBrace_478 | C_hkLt_480 | C_hkGt_482 | C_hkEq_484 |
    C_hkBang_486 | C_hkLParen_488 | C_hkRParen_490 | C_hkRBrace_492 |
    C_hkColon_494 | C_hkLambda_496 | C_hkComma_498 | C_hkSemi_500 |
    C_hkAt_502 | C_hkPipe_504 | C_hkPlus_506 | C_hkStar_508 |
    C_hkSlash_510 | C_hkPct_512 | C_hkAmp_514 | C_hkDot_516 |
    C_hkStr_518 | C_hkGen_520
-- Once.Parser.Lexer.headK
d_headK_522 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> T_HeadK_468
d_headK_522 v0
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
      (coe C_hkWS_470)
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
               (coe '\n')))
         (coe C_hkNL_472)
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                  (coe '^')))
            (coe C_hkCaret_474)
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                  (coe
                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                     (coe '-')))
               (coe C_hkDash_476)
               (coe
                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                        (coe '{')))
                  (coe C_hkLBrace_478)
                  (coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe
                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                           (coe '<')))
                     (coe C_hkLt_480)
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                              (coe '>')))
                        (coe C_hkGt_482)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                 (coe '=')))
                           (coe C_hkEq_484)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                    (coe '!')))
                              (coe C_hkBang_486)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                       (coe '(')))
                                 (coe C_hkLParen_488)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                          (coe ')')))
                                    (coe C_hkRParen_490)
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                             (coe v0) (coe '}')))
                                       (coe C_hkRBrace_492)
                                       (coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                             (coe
                                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                (coe v0) (coe ':')))
                                          (coe C_hkColon_494)
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                (coe
                                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                   (coe v0) (coe '\\')))
                                             (coe C_hkLambda_496)
                                             (coe
                                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                      (coe v0) (coe ',')))
                                                (coe C_hkComma_498)
                                                (coe
                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                      (coe
                                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                         (coe v0) (coe ';')))
                                                   (coe C_hkSemi_500)
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                         (coe
                                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                            (coe v0) (coe '@')))
                                                      (coe C_hkAt_502)
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                            (coe
                                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                               (coe v0) (coe '|')))
                                                         (coe C_hkPipe_504)
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                               (coe
                                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                  (coe v0) (coe '+')))
                                                            (coe C_hkPlus_506)
                                                            (coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                  (coe
                                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                     (coe v0) (coe '*')))
                                                               (coe C_hkStar_508)
                                                               (coe
                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                        (coe v0) (coe '/')))
                                                                  (coe C_hkSlash_510)
                                                                  (coe
                                                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                        (coe
                                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                           (coe v0) (coe '%')))
                                                                     (coe C_hkPct_512)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                           (coe
                                                                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                              (coe v0) (coe '&')))
                                                                        (coe C_hkAmp_514)
                                                                        (coe
                                                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                 (coe v0)
                                                                                 (coe '.')))
                                                                           (coe C_hkDot_516)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                                                    (coe v0)
                                                                                    (coe '"')))
                                                                              (coe C_hkStr_518)
                                                                              (coe
                                                                                 C_hkGen_520)))))))))))))))))))))))))
-- Once.Parser.Lexer.tok-str
d_tok'45'str_536 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'str_536 v0 v1 ~v2 v3 = du_tok'45'str_536 v0 v1 v3
du_tok'45'str_536 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'str_536 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Parser.Token.C_TString_14
                              (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v4))
                           (coe
                              du_tokenize'45'WF_634 (coe v6)
                              (coe d_adv_622 (coe v0) (coe v6) (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-gen
d_tok'45'gen_546 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'gen_546 v0 v1 v2 ~v3 v4 v5
  = du_tok'45'gen_546 v0 v1 v2 v4 v5
du_tok'45'gen_546 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'gen_546 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_tok'45'num_564 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_collectDigitsB_72 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_collectDigitsB_72 (coe v1))))
             (coe
                d_collectFracB_102
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_collectDigitsB_72 (coe v1)))))
      else (if coe v4
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
                                 (coe d_collectIdentB_38 (coe v1))))))
                     (coe
                        du_tokenize'45'WF_634
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_collectIdentB_38 (coe v1))))
                        (coe
                           d_adv_622 (coe v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_collectIdentB_38 (coe v1))))
                           (coe v2)))
              else coe
                     du_tokenize'45'WF_634 (coe v1)
                     (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
-- Once.Parser.Lexer.tok-num
d_tok'45'num_564 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'num_564 v0 v1 v2 ~v3 v4 v5 ~v6 v7
  = du_tok'45'num_564 v0 v1 v2 v4 v5 v7
du_tok'45'num_564 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'num_564 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Parser.Token.C_TFloat_12
                              (coe
                                 d_digitsToNat_134
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
                              (coe d_digitsToNat_134 v7)
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v7) (coe v2))
                           (coe
                              du_tokenize'45'WF_634 (coe v9)
                              (coe d_adv_622 (coe v1) (coe v9) (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TInt_10
                (coe
                   d_digitsToNat_134
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
                (coe v2))
             (coe
                du_tokenize'45'WF_634 (coe v4)
                (coe d_adv_622 (coe v1) (coe v4) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-nl
d_tok'45'nl_572 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'nl_572 v0 v1 ~v2 v3 = du_tok'45'nl_572 v0 v1 v3
du_tok'45'nl_572 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'nl_572 v0 v1 v2
  = if coe v2
      then coe
             du_tokenize'45'WF_634 (coe v0)
             (coe d_adv_622 (coe v0) (coe v0) (coe v1))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_74)
             (coe
                du_tokenize'45'WF_634 (coe v0)
                (coe d_adv_622 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.tok-op2
d_tok'45'op2_580 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'op2_580 v0 v1 ~v2 v3 v4 v5
  = du_tok'45'op2_580 v0 v1 v3 v4 v5
du_tok'45'op2_580 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'op2_580 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe
                du_tokenize'45'WF_634 (coe d_drop1_458 (coe v0))
                (coe d_adv_622 (coe v0) (coe d_drop1_458 (coe v0)) (coe v1)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
             (coe
                du_tokenize'45'WF_634 (coe v0)
                (coe d_adv_622 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.tok-lbrace
d_tok'45'lbrace_588 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'lbrace_588 v0 v1 ~v2 v3 = du_tok'45'lbrace_588 v0 v1 v3
du_tok'45'lbrace_588 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'lbrace_588 v0 v1 v2
  = if coe v2
      then coe
             du_tokenize'45'WF_634
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_skipBlockB_398 (coe (1 :: Integer)) (coe d_drop1_458 (coe v0))))
             (coe
                d_adv_622 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_skipBlockB_398 (coe (1 :: Integer)) (coe d_drop1_458 (coe v0))))
                (coe v1))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_20)
             (coe
                du_tokenize'45'WF_634 (coe v0)
                (coe d_adv_622 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.tok-minus
d_tok'45'minus_596 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Dash3_420 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'minus_596 v0 v1 ~v2 v3 = du_tok'45'minus_596 v0 v1 v3
du_tok'45'minus_596 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_Dash3_420 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'minus_596 v0 v1 v2
  = case coe v2 of
      C_d'45'comment_422
        -> coe
             du_tokenize'45'WF_634
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_skipLineB_286 (coe d_drop1_458 (coe v0))))
             (coe
                d_adv_622 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_skipLineB_286 (coe d_drop1_458 (coe v0))))
                (coe v1))
      C_d'45'arrow_424
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
             (coe
                du_tokenize'45'WF_634 (coe d_drop1_458 (coe v0))
                (coe d_adv_622 (coe v0) (coe d_drop1_458 (coe v0)) (coe v1)))
      C_d'45'minus_426
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TMinus_50)
             (coe
                du_tokenize'45'WF_634 (coe v0)
                (coe d_adv_622 (coe v0) (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-caret
d_tok'45'caret_604 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Caret4_428 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'caret_604 v0 v1 ~v2 v3 = du_tok'45'caret_604 v0 v1 v3
du_tok'45'caret_604 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_Caret4_428 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'caret_604 v0 v1 v2
  = case coe v2 of
      C_c'45'1_430
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_30)
             (coe
                du_tokenize'45'WF_634 (coe d_drop1_458 (coe v0))
                (coe d_adv_622 (coe v0) (coe d_drop1_458 (coe v0)) (coe v1)))
      C_c'45'0_432
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_32)
             (coe
                du_tokenize'45'WF_634 (coe d_drop1_458 (coe v0))
                (coe d_adv_622 (coe v0) (coe d_drop1_458 (coe v0)) (coe v1)))
      C_c'45'w_434
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_34)
             (coe
                du_tokenize'45'WF_634 (coe d_drop1_458 (coe v0))
                (coe d_adv_622 (coe v0) (coe d_drop1_458 (coe v0)) (coe v1)))
      C_c'45'gen_436
        -> coe
             du_tok'45'gen_546 (coe '^') (coe v0) (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 '^')
             (coe d_isIdentStart_8 (coe '^'))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-head
d_tok'45'head_614 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_HeadK_468 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'head_614 v0 v1 v2 ~v3 v4 = du_tok'45'head_614 v0 v1 v2 v4
du_tok'45'head_614 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_HeadK_468 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'head_614 v0 v1 v2 v3
  = case coe v3 of
      C_hkWS_470
        -> coe
             du_tokenize'45'WF_634 (coe v1)
             (coe d_adv_622 (coe v1) (coe v1) (coe v2))
      C_hkNL_472
        -> coe
             du_tok'45'nl_572 (coe v1) (coe v2) (coe d_nlIndent_438 (coe v1))
      C_hkCaret_474
        -> coe
             du_tok'45'caret_604 (coe v1) (coe v2)
             (coe d_caretClass_454 (coe v1))
      C_hkDash_476
        -> coe
             du_tok'45'minus_596 (coe v1) (coe v2)
             (coe d_dashClass_450 (coe v1))
      C_hkLBrace_478
        -> coe
             du_tok'45'lbrace_588 (coe v1) (coe v2)
             (coe d_isDashHead_446 (coe v1))
      C_hkLt_480
        -> coe
             du_tok'45'op2_580 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Token.C_TLe_62)
             (coe MAlonzo.Code.Once.Parser.Token.C_TLt_60)
             (coe d_isEqHead_442 (coe v1))
      C_hkGt_482
        -> coe
             du_tok'45'op2_580 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Token.C_TGe_66)
             (coe MAlonzo.Code.Once.Parser.Token.C_TGt_64)
             (coe d_isEqHead_442 (coe v1))
      C_hkEq_484
        -> coe
             du_tok'45'op2_580 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEqEq_68)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_26)
             (coe d_isEqHead_442 (coe v1))
      C_hkBang_486
        -> coe
             du_tok'45'op2_580 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.Token.C_TNeq_70)
             (coe MAlonzo.Code.Once.Parser.Token.C_TBang_72)
             (coe d_isEqHead_442 (coe v1))
      C_hkLParen_488
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkRParen_490
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkRBrace_492
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkColon_494
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkLambda_496
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_36)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkComma_498
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkSemi_500
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkAt_502
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAt_42)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkPipe_504
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPipe_44)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkPlus_506
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPlus_48)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkStar_508
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TStar_52)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkSlash_510
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TSlash_54)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkPct_512
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPercent_56)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkAmp_514
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkDot_516
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
             (coe
                du_tokenize'45'WF_634 (coe v1)
                (coe d_adv_622 (coe v1) (coe v1) (coe v2)))
      C_hkStr_518
        -> coe
             du_tok'45'str_536 (coe v1) (coe v2)
             (coe d_collectStringB_160 (coe v1))
      C_hkGen_520
        -> coe
             du_tok'45'gen_546 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
             (coe d_isIdentStart_8 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.adv
d_adv_622 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer -> Integer
d_adv_622 v0 v1 v2
  = coe
      addInt
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (addInt
            (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
      (coe v2)
-- Once.Parser.Lexer.tokenize-WF
d_tokenize'45'WF_634 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize'45'WF_634 v0 v1 ~v2 = du_tokenize'45'WF_634 v0 v1
du_tokenize'45'WF_634 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tokenize'45'WF_634 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TEOF_76) (coe v0)
      (:) v2 v3
        -> coe
             du_tok'45'head_614 (coe v2) (coe v3) (coe v1)
             (coe d_headK_522 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tokenize
d_tokenize_1028 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize_1028 v0
  = coe du_tokenize'45'WF_634 (coe v0) (coe (0 :: Integer))
-- Once.Parser.Lexer.tokenizeString
d_tokenizeString_1032 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenizeString_1032 v0
  = coe
      d_tokenize_1028
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
