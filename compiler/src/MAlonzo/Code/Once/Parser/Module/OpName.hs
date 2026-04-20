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

module MAlonzo.Code.Once.Parser.Module.OpName where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Module.OpName.parseOpCharsB
d_parseOpCharsB_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpCharsB_10 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TRParen_16
                  -> case coe v1 of
                       [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       (:) v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                    (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_foldr_216
                                             (let v7
                                                    = \ v7 ->
                                                        addInt (coe (1 :: Integer)) (coe v7) in
                                              coe (coe (\ v8 -> v7)))
                                             (coe (0 :: Integer)) (coe v4))))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Parser.Token.C_TAt_40
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '@')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TPipe_42
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '|')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TDot_44
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TPlus_46
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '+')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TMinus_48
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TStar_50
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '*')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TSlash_52
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '/')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TPercent_54
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TAmpersand_56
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '&')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TLt_58
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '<')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TGt_62
                  -> let v5
                           = d_parseOpCharsB_10
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '>')
                                  (coe v1)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v11 v12 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v12)))
                                                           (coe (0 :: Integer)) (coe v4))
                                                        (coe v10)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v11 v12 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v12)))
                                                                 (coe (0 :: Integer)) (coe v4)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.Module.OpName.parseOpChars
d_parseOpChars_262 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpChars_262 v0 v1
  = let v2 = d_parseOpCharsB_10 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.OpName.parseOperatorNameB
d_parseOperatorNameB_286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorNameB_286 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_14
                  -> let v4
                           = d_parseOpCharsB_10
                               (coe v3) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v10 v11 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v11)))
                                                           (coe (0 :: Integer)) (coe v3))
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v10 v11 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v11)))
                                                                 (coe (0 :: Integer)) (coe v3)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Module.OpName.parseOperatorName
d_parseOperatorName_304 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorName_304 v0
  = let v1 = d_parseOperatorNameB_286 (coe v0) in
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
