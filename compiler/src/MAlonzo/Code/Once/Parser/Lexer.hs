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
import qualified MAlonzo.Code.Once.Name.Chars
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Surface.Lexing
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Parser.Lexer.Bounded
d_Bounded_6 :: () -> Integer -> ()
d_Bounded_6 = erased
-- Once.Parser.Lexer.BoundedStrict
d_BoundedStrict_16 :: () -> Integer -> ()
d_BoundedStrict_16 = erased
-- Once.Parser.Lexer.collectIdentB
d_collectIdentB_28 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdentB_28 v0
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
                           (coe
                              eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                              (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '_'))
                           (coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                                 (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '\''))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe
                                    eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                                    (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '+'))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                    (coe
                                       eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                                       (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '*'))
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                       (coe
                                          eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                                          (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '!'))
                                       (coe
                                          eqInt (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 v1)
                                          (coe MAlonzo.Code.Once.Name.Chars.d_toNat_6 '?')))))))) in
           coe
             (if coe v3
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe d_collectIdentB_28 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_28 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectIdentB_28 (coe v2)))))
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
d_collectIdent_52 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectIdent_52 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectIdentB_28 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectIdentB_28 (coe v0))))
-- Once.Parser.Lexer.collectDigitsB
d_collectDigitsB_62 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigitsB_62 v0
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
                             (coe d_collectDigitsB_62 (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_62 (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe d_collectDigitsB_62 (coe v2)))))
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
d_collectFracB_92 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectFracB_92 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_frac'45'dot_100
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v1)
                (coe '.'))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.frac-dot
d_frac'45'dot_100 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_frac'45'dot_100 v0 v1
  = if coe v0
      then case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v2 v3
               -> coe
                    d_frac'45'digit_110
                    (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v2) (coe v2)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Parser.Lexer.frac-digit
d_frac'45'digit_110 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_frac'45'digit_110 v0 v1 v2
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_collectDigitsB_62 (coe v2))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_collectDigitsB_62 (coe v2))))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_collectDigitsB_62 (coe v2)))))))
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Parser.Lexer.collectDigits
d_collectDigits_134 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectDigits_134 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_collectDigitsB_62 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_collectDigitsB_62 (coe v0))))
-- Once.Parser.Lexer.digitsToNat
d_digitsToNat_142 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer
d_digitsToNat_142
  = coe MAlonzo.Code.Once.Spec.Surface.Lexing.d_digitsToNat_82
-- Once.Parser.Lexer.collectStringB
d_collectStringB_150 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectStringB_150 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_str'45'char_186
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v1)
                (coe '"'))
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v1)
                (coe '\\'))
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.escChar
d_escChar_152 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_escChar_152 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v0)
         (coe 'n'))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe '\n'))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v0)
            (coe 't'))
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe '\t'))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v0)
               (coe 'r'))
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe '\r'))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v0)
                  (coe '\\'))
               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe '\\'))
               (coe
                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                  (coe
                     MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v0)
                     (coe '"'))
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe '"'))
                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
-- Once.Parser.Lexer.str-cons
d_str'45'cons_166 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_str'45'cons_166 ~v0 v1 v2 = du_str'45'cons_166 v1 v2
du_str'45'cons_166 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_str'45'cons_166 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v3))
                          (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.str-char
d_str'45'char_186 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_str'45'char_186 v0 v1 v2 v3
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                         (coe
                            MAlonzo.Code.Data.List.Base.du_foldr_216
                            (let v4 = \ v4 -> addInt (coe (1 :: Integer)) (coe v4) in
                             coe (coe (\ v5 -> v4)))
                            (coe (0 :: Integer)) (coe v3))))))
      else (if coe v1
              then coe d_str'45'esc_194 (coe v3)
              else coe
                     du_str'45'cons_166
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                     (coe d_collectStringB_150 (coe v3)))
-- Once.Parser.Lexer.str-esc
d_str'45'esc_194 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_str'45'esc_194 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_str'45'esc'8242'_204 (coe d_escChar_152 (coe v1)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.str-esc′
d_str'45'esc'8242'_204 ::
  Maybe MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_str'45'esc'8242'_204 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_str'45'cons_166
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                du_str'45'cons_166
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe d_collectStringB_150 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_str'45'cons_166
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\\')
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                du_str'45'cons_166
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe d_collectStringB_150 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.collectString
d_collectString_236 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_collectString_236 v0
  = let v1 = d_collectStringB_150 (coe v0) in
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
d_skipLineB_256 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipLineB_256 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (:) v1 v2
        -> coe
             d_skip'45'nl_264
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'61''61'__26 (coe v1)
                (coe '\n'))
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.skip-nl
d_skip'45'nl_264 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skip'45'nl_264 v0 v1 v2
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_skipLineB_256 (coe v2)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_skipLineB_256 (coe v2)))
-- Once.Parser.Lexer.skipLine
d_skipLine_282 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipLine_282 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipLineB_256 (coe v0))
-- Once.Parser.Lexer.skipLine-length
d_skipLine'45'length_288 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipLine'45'length_288 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipLineB_256 (coe v0))
-- Once.Parser.Lexer.skipBlockB-WF
d_skipBlockB'45'WF_296 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB'45'WF_296 v0 v1 ~v2 = du_skipBlockB'45'WF_296 v0 v1
du_skipBlockB'45'WF_296 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_skipBlockB'45'WF_296 v0 v1
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
                                 (coe du_skipBlockB'45'WF_296 (coe v0) (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe du_skipBlockB'45'WF_296 (coe v0) (coe v4)))
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
                                                 du_skipBlockB'45'WF_296
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 du_skipBlockB'45'WF_296
                                                 (coe addInt (coe (1 :: Integer)) (coe v0))
                                                 (coe v6)))
                                    else (if coe v8
                                            then coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_296 (coe v2) (coe v6)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_296 (coe v2) (coe v6)))
                                            else coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_skipBlockB'45'WF_296 (coe v0) (coe v4)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         du_skipBlockB'45'WF_296 (coe v0)
                                                         (coe v4))))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Lexer.skipBlockB
d_skipBlockB_370 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipBlockB_370 v0 v1
  = coe du_skipBlockB'45'WF_296 (coe v0) (coe v1)
-- Once.Parser.Lexer.skipBlock
d_skipBlock_376 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_skipBlock_376 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_skipBlockB_370 (coe v0) (coe v1))
-- Once.Parser.Lexer.skipBlock-length
d_skipBlock'45'length_386 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_skipBlock'45'length_386 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_skipBlockB_370 (coe v0) (coe v1))
-- Once.Parser.Lexer.Dash3
d_Dash3_392 = ()
data T_Dash3_392
  = C_d'45'comment_394 | C_d'45'arrow_396 | C_d'45'minus_398
-- Once.Parser.Lexer.Caret4
d_Caret4_400 = ()
data T_Caret4_400
  = C_c'45'1_402 | C_c'45'0_404 | C_c'45'w_406 | C_c'45'gen_408
-- Once.Parser.Lexer.nlIndent
d_nlIndent_410 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_nlIndent_410 v0
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
d_isEqHead_414 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isEqHead_414 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '='))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.isDotHead
d_isDotHead_418 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isDotHead_418 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '.'))
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
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Dash3_392
d_dashClass_426 v0
  = case coe v0 of
      [] -> coe C_d'45'minus_398
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '-')))
             (coe C_d'45'comment_394)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '>')))
                (coe C_d'45'arrow_396) (coe C_d'45'minus_398))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.caretClass
d_caretClass_430 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_Caret4_400
d_caretClass_430 v0
  = case coe v0 of
      [] -> coe C_c'45'gen_408
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe '1')))
             (coe C_c'45'1_402)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '0')))
                (coe C_c'45'0_404)
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                      (coe
                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                         (coe 'w')))
                   (coe C_c'45'w_406) (coe C_c'45'gen_408)))
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
d_tok'45'str_512 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'str_512 v0 v1 ~v2 v3 = du_tok'45'str_512 v0 v1 v3
du_tok'45'str_512 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'str_512 v0 v1 v2
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
                              du_tokenize'45'WF_628 (coe v6)
                              (coe d_adv_616 (coe v0) (coe v6) (coe v1)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-gen
d_tok'45'gen_522 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'gen_522 v0 v1 v2 ~v3 v4 v5
  = du_tok'45'gen_522 v0 v1 v2 v4 v5
du_tok'45'gen_522 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  Bool -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'gen_522 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_tok'45'num_540 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_collectDigitsB_62 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_collectDigitsB_62 (coe v1))))
             (coe
                d_collectFracB_92
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe d_collectDigitsB_62 (coe v1)))))
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
                                 (coe d_collectIdentB_28 (coe v1))))))
                     (coe
                        du_tokenize'45'WF_628
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe d_collectIdentB_28 (coe v1))))
                        (coe
                           d_adv_616 (coe v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe d_collectIdentB_28 (coe v1))))
                           (coe v2)))
              else coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Parser.Lexer.tok-num
d_tok'45'num_540 ::
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
d_tok'45'num_540 v0 v1 v2 ~v3 v4 v5 ~v6 v7
  = du_tok'45'num_540 v0 v1 v2 v4 v5 v7
du_tok'45'num_540 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'num_540 v0 v1 v2 v3 v4 v5
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
                                 d_digitsToNat_142
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
                              (coe d_digitsToNat_142 v7)
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v7) (coe v2))
                           (coe
                              du_tokenize'45'WF_628 (coe v9)
                              (coe d_adv_616 (coe v1) (coe v9) (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TInt_10
                (coe
                   d_digitsToNat_142
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
                (coe v2))
             (coe
                du_tokenize'45'WF_628 (coe v4)
                (coe d_adv_616 (coe v1) (coe v4) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-nl
d_tok'45'nl_548 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'nl_548 v0 v1 ~v2 v3 = du_tok'45'nl_548 v0 v1 v3
du_tok'45'nl_548 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'nl_548 v0 v1 v2
  = if coe v2
      then coe
             du_tokenize'45'WF_628 (coe v0)
             (coe d_adv_616 (coe v0) (coe v0) (coe v1))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_56)
             (coe
                du_tokenize'45'WF_628 (coe v0)
                (coe d_adv_616 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.tok-lbrace
d_tok'45'lbrace_556 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'lbrace_556 v0 v1 ~v2 v3 = du_tok'45'lbrace_556 v0 v1 v3
du_tok'45'lbrace_556 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'lbrace_556 v0 v1 v2
  = if coe v2
      then coe
             du_tokenize'45'WF_628
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_skipBlockB_370 (coe (1 :: Integer)) (coe d_drop1_434 (coe v0))))
             (coe
                d_adv_616 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_skipBlockB_370 (coe (1 :: Integer)) (coe d_drop1_434 (coe v0))))
                (coe v1))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLBrace_20)
             (coe
                du_tokenize'45'WF_628 (coe v0)
                (coe d_adv_616 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.tok-minus
d_tok'45'minus_564 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Dash3_392 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'minus_564 v0 v1 ~v2 v3 = du_tok'45'minus_564 v0 v1 v3
du_tok'45'minus_564 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_Dash3_392 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'minus_564 v0 v1 v2
  = case coe v2 of
      C_d'45'comment_394
        -> coe
             du_tokenize'45'WF_628
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_skipLineB_256 (coe d_drop1_434 (coe v0))))
             (coe
                d_adv_616 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_skipLineB_256 (coe d_drop1_434 (coe v0))))
                (coe v1))
      C_d'45'arrow_396
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TArrow_28)
             (coe
                du_tokenize'45'WF_628 (coe d_drop1_434 (coe v0))
                (coe d_adv_616 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)))
      C_d'45'minus_398
        -> coe
             du_tok'45'dot_592 (coe v0) (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12)
             (coe d_isDotHead_418 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-caret
d_tok'45'caret_572 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_Caret4_400 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'caret_572 v0 v1 ~v2 v3 = du_tok'45'caret_572 v0 v1 v3
du_tok'45'caret_572 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_Caret4_400 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'caret_572 v0 v1 v2
  = case coe v2 of
      C_c'45'1_402
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret1_30)
             (coe
                du_tokenize'45'WF_628 (coe d_drop1_434 (coe v0))
                (coe d_adv_616 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)))
      C_c'45'0_404
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaret0_32)
             (coe
                du_tokenize'45'WF_628 (coe d_drop1_434 (coe v0))
                (coe d_adv_616 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)))
      C_c'45'w_406
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TCaretW_34)
             (coe
                du_tokenize'45'WF_628 (coe d_drop1_434 (coe v0))
                (coe d_adv_616 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)))
      C_c'45'gen_408 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-head
d_tok'45'head_582 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  T_HeadK_444 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'head_582 v0 v1 v2 ~v3 v4 = du_tok'45'head_582 v0 v1 v2 v4
du_tok'45'head_582 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  T_HeadK_444 -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'head_582 v0 v1 v2 v3
  = case coe v3 of
      C_hkWS_446
        -> coe
             du_tokenize'45'WF_628 (coe v1)
             (coe d_adv_616 (coe v1) (coe v1) (coe v2))
      C_hkNL_448
        -> coe
             du_tok'45'nl_548 (coe v1) (coe v2) (coe d_nlIndent_410 (coe v1))
      C_hkCaret_450
        -> coe
             du_tok'45'caret_572 (coe v1) (coe v2)
             (coe d_caretClass_430 (coe v1))
      C_hkDash_452
        -> coe
             du_tok'45'minus_564 (coe v1) (coe v2)
             (coe d_dashClass_426 (coe v1))
      C_hkLBrace_454
        -> coe
             du_tok'45'lbrace_556 (coe v1) (coe v2)
             (coe d_isDashHead_422 (coe v1))
      C_hkLt_456
        -> coe
             du_tok'45'cmp_600 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60''61'_20)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18)
             (coe d_isEqHead_414 (coe v1))
      C_hkGt_458
        -> coe
             du_tok'45'cmp_600 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22)
             (coe d_isEqHead_414 (coe v1))
      C_hkEq_460
        -> coe
             du_tok'45'eqop_608 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26)
             (coe MAlonzo.Code.Once.Parser.Token.C_TEquals_26)
             (coe d_isEqHead_414 (coe v1))
      C_hkBang_462
        -> coe
             du_tok'45'eqop_608 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28)
             (coe MAlonzo.Code.Once.Parser.Token.C_TBang_54)
             (coe d_isEqHead_414 (coe v1))
      C_hkLParen_464
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLParen_16)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkRParen_466
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_18)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkRBrace_468
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TRBrace_22)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkColon_470
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TColon_24)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkLambda_472
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TLambda_36)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkComma_474
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TComma_38)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkSemi_476
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkAt_478
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAt_42)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkPipe_480
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TPipe_44)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkPlus_482
        -> coe
             du_tok'45'dot_592 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10)
             (coe d_isDotHead_418 (coe v1))
      C_hkStar_484
        -> coe
             du_tok'45'dot_592 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14)
             (coe d_isDotHead_418 (coe v1))
      C_hkSlash_486
        -> coe
             du_tok'45'dot_592 (coe v1) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16)
             (coe d_isDotHead_418 (coe v1))
      C_hkPct_488
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TOp_48
                (coe MAlonzo.Code.Once.Spec.Surface.Operator.C_o'37'_34))
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkAmp_490
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TAmpersand_52)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkDot_492
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TDot_46)
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v1) (coe v1) (coe v2)))
      C_hkStr_494
        -> coe
             du_tok'45'str_512 (coe v1) (coe v2)
             (coe d_collectStringB_150 (coe v1))
      C_hkGen_496
        -> coe
             du_tok'45'gen_522 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v0)
             (coe MAlonzo.Code.Once.Name.Chars.d_isIdentStart_8 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tok-dot
d_tok'45'dot_592 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'dot_592 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_tok'45'dot_592 v0 v1 v2 v5 v6
du_tok'45'dot_592 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'dot_592 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TOpD_50 (coe v3))
             (coe
                du_tokenize'45'WF_628 (coe d_drop1_434 (coe v1))
                (coe d_adv_616 (coe v0) (coe d_drop1_434 (coe v1)) (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Parser.Token.C_TOp_48
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32
                   (coe v3)))
             (coe
                du_tokenize'45'WF_628 (coe v1)
                (coe d_adv_616 (coe v0) (coe v1) (coe v2)))
-- Once.Parser.Lexer.tok-cmp
d_tok'45'cmp_600 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'cmp_600 v0 v1 ~v2 v3 v4 v5
  = du_tok'45'cmp_600 v0 v1 v3 v4 v5
du_tok'45'cmp_600 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'cmp_600 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_tok'45'dot_592 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)
             (coe v2) (coe d_isDotHead_418 (coe d_drop1_434 (coe v0)))
      else coe
             du_tok'45'dot_592 (coe v0) (coe v0) (coe v1) (coe v3)
             (coe d_isDotHead_418 (coe v0))
-- Once.Parser.Lexer.tok-eqop
d_tok'45'eqop_608 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tok'45'eqop_608 v0 v1 ~v2 v3 v4 v5
  = du_tok'45'eqop_608 v0 v1 v3 v4 v5
du_tok'45'eqop_608 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_Dottable_8 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  Bool -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tok'45'eqop_608 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_tok'45'dot_592 (coe v0) (coe d_drop1_434 (coe v0)) (coe v1)
             (coe v2) (coe d_isDotHead_418 (coe d_drop1_434 (coe v0)))
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
             (coe
                du_tokenize'45'WF_628 (coe v0)
                (coe d_adv_616 (coe v0) (coe v0) (coe v1)))
-- Once.Parser.Lexer.adv
d_adv_616 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Integer -> Integer
d_adv_616 v0 v1 v2
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
d_tokenize'45'WF_628 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize'45'WF_628 v0 v1 ~v2 = du_tokenize'45'WF_628 v0 v1
du_tokenize'45'WF_628 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Integer -> [MAlonzo.Code.Once.Parser.Token.T_Token_6]
du_tokenize'45'WF_628 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.Token.C_TEOF_58) (coe v0)
      (:) v2 v3
        -> coe
             du_tok'45'head_582 (coe v2) (coe v3) (coe v1)
             (coe d_headK_498 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Lexer.tokenize
d_tokenize_1066 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenize_1066 v0
  = coe du_tokenize'45'WF_628 (coe v0) (coe (0 :: Integer))
-- Once.Parser.Lexer.tokenizeString
d_tokenizeString_1070 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6]
d_tokenizeString_1070 v0
  = coe
      d_tokenize_1066
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
