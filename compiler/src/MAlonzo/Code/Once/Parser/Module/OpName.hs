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
import qualified MAlonzo.Code.Once.Spec.Surface.Operator

-- Once.Parser.Module.OpName.OpTok
d_OpTok_8 = ()
data T_OpTok_8
  = C_otClose_10 |
    C_otChar_12 MAlonzo.Code.Agda.Builtin.Char.T_Char_6 |
    C_otDotted_14 MAlonzo.Code.Agda.Builtin.Char.T_Char_6 | C_otNone_16
-- Once.Parser.Module.OpName.opTokClass
d_opTokClass_18 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> T_OpTok_8
d_opTokClass_18 v0
  = let v1 = coe C_otNone_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TRParen_18 -> coe C_otClose_10
         MAlonzo.Code.Once.Parser.Token.C_TAt_42
           -> coe C_otChar_12 (coe '@')
         MAlonzo.Code.Once.Parser.Token.C_TPipe_44
           -> coe C_otChar_12 (coe '|')
         MAlonzo.Code.Once.Parser.Token.C_TDot_46
           -> coe C_otChar_12 (coe '.')
         MAlonzo.Code.Once.Parser.Token.C_TOp_48 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
                         -> coe C_otChar_12 (coe '+')
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
                         -> coe C_otChar_12 (coe '-')
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
                         -> coe C_otChar_12 (coe '*')
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16
                         -> coe C_otChar_12 (coe '/')
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18
                         -> coe C_otChar_12 (coe '<')
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
                         -> coe C_otChar_12 (coe '>')
                       _ -> coe v1
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'37'_34
                  -> coe C_otChar_12 (coe '%')
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Parser.Token.C_TOpD_50 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
                  -> coe C_otDotted_14 (coe '+')
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
                  -> coe C_otDotted_14 (coe '-')
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
                  -> coe C_otDotted_14 (coe '*')
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16
                  -> coe C_otDotted_14 (coe '/')
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18
                  -> coe C_otDotted_14 (coe '<')
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
                  -> coe C_otDotted_14 (coe '>')
                _ -> coe v1
         MAlonzo.Code.Once.Parser.Token.C_TAmpersand_52
           -> coe C_otChar_12 (coe '&')
         _ -> coe v1)
-- Once.Parser.Module.OpName.pocStep
d_pocStep_24 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocStep_24 ~v0 v1 v2 = du_pocStep_24 v1 v2
du_pocStep_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocStep_24 v0 v1
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
d_pocClose_44 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocClose_44 ~v0 v1 v2 = du_pocClose_44 v1 v2
du_pocClose_44 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocClose_44 v0 v1
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
d_parseOpCharsB_60 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpCharsB_60 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> coe du_pocGo_68 (coe v3) (coe v1) (coe d_opTokClass_18 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.pocGo
d_pocGo_68 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_OpTok_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pocGo_68 ~v0 v1 v2 v3 = du_pocGo_68 v1 v2 v3
du_pocGo_68 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  T_OpTok_8 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pocGo_68 v0 v1 v2
  = case coe v2 of
      C_otClose_10 -> coe du_pocClose_44 (coe v0) (coe v1)
      C_otChar_12 v3
        -> coe
             du_pocStep_24 (coe v0)
             (coe
                d_parseOpCharsB_60 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1)))
      C_otDotted_14 v3
        -> coe
             du_pocStep_24 (coe v0)
             (coe
                d_parseOpCharsB_60 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))))
      C_otNone_16 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.OpName.parseOpChars
d_parseOpChars_106 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOpChars_106 v0 v1
  = let v2 = d_parseOpCharsB_60 (coe v0) (coe v1) in
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
d_parseOperatorNameB_130 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorNameB_130 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> let v4
                           = d_parseOpCharsB_60
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
d_parseOperatorName_148 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseOperatorName_148 v0
  = let v1 = d_parseOperatorNameB_130 (coe v0) in
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
