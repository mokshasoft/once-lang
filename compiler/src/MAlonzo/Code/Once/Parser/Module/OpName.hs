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

-- Once.Parser.Module.OpName.OpTok
d_OpTok_8 = ()
data T_OpTok_8
  = C_otClose_10 |
    C_otChar_12 MAlonzo.Code.Agda.Builtin.Char.T_Char_6 | C_otNone_14
-- Once.Parser.Module.OpName.opTokClass
d_opTokClass_16 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> T_OpTok_8
d_opTokClass_16 v0
  = let v1 = coe C_otNone_14 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TRParen_18 -> coe C_otClose_10
         MAlonzo.Code.Once.Parser.Token.C_TAt_42
           -> coe C_otChar_12 (coe '@')
         MAlonzo.Code.Once.Parser.Token.C_TPipe_44
           -> coe C_otChar_12 (coe '|')
         MAlonzo.Code.Once.Parser.Token.C_TDot_46
           -> coe C_otChar_12 (coe '.')
         MAlonzo.Code.Once.Parser.Token.C_TPlus_48
           -> coe C_otChar_12 (coe '+')
         MAlonzo.Code.Once.Parser.Token.C_TMinus_50
           -> coe C_otChar_12 (coe '-')
         MAlonzo.Code.Once.Parser.Token.C_TStar_52
           -> coe C_otChar_12 (coe '*')
         MAlonzo.Code.Once.Parser.Token.C_TSlash_54
           -> coe C_otChar_12 (coe '/')
         MAlonzo.Code.Once.Parser.Token.C_TPercent_56
           -> coe C_otChar_12 (coe '%')
         MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
           -> coe C_otChar_12 (coe '&')
         MAlonzo.Code.Once.Parser.Token.C_TLt_60
           -> coe C_otChar_12 (coe '<')
         MAlonzo.Code.Once.Parser.Token.C_TGt_64
           -> coe C_otChar_12 (coe '>')
         _ -> coe v1)
-- Once.Parser.Module.OpName.pocStep
d_pocStep_22 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocStep_22 ~v0 v1 v2 = du_pocStep_22 v1 v2
du_pocStep_22 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocStep_22 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v0) (coe v6)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_foldr_216
                                             (let v7
                                                    = \ v7 ->
                                                        addInt (coe (1 :: Integer)) (coe v7) in
                                              coe (coe (\ v8 -> v7)))
                                             (coe (0 :: Integer)) (coe v0)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.pocClose
d_pocClose_42 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocClose_42 ~v0 v1 v2 = du_pocClose_42 v1 v2
du_pocClose_42 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocClose_42 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                   (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                         (coe
                            MAlonzo.Code.Data.List.Base.du_foldr_216
                            (let v4 = \ v4 -> addInt (coe (1 :: Integer)) (coe v4) in
                             coe (coe (\ v5 -> v4)))
                            (coe (0 :: Integer)) (coe v0))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.parseOpCharsB
d_parseOpCharsB_58 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpCharsB_58 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> coe du_pocGo_66 (coe v3) (coe v1) (coe d_opTokClass_16 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.pocGo
d_pocGo_66 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_OpTok_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocGo_66 ~v0 v1 v2 v3 = du_pocGo_66 v1 v2 v3
du_pocGo_66 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_OpTok_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocGo_66 v0 v1 v2
  = case coe v2 of
      C_otClose_10 -> coe du_pocClose_42 (coe v0) (coe v1)
      C_otChar_12 v3
        -> coe
             du_pocStep_22 (coe v0)
             (coe
                d_parseOpCharsB_58 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1)))
      C_otNone_14 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.parseOpChars
d_parseOpChars_96 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpChars_96 v0 v1
  = let v2 = d_parseOpCharsB_58 (coe v0) (coe v1) in
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
d_parseOperatorNameB_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorNameB_120 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> let v4
                           = d_parseOpCharsB_58
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
d_parseOperatorName_138 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorName_138 v0
  = let v1 = d_parseOperatorNameB_120 (coe v0) in
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
