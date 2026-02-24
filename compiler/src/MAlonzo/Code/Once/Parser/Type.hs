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

module MAlonzo.Code.Once.Parser.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Parser.Type.isUpperWord
d_isUpperWord_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isUpperWord_6 v0
  = let v1
          = coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 in
    coe
      (case coe v1 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         (:) v2 v3
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v2)
                (coe
                   MAlonzo.Code.Data.Bool.Base.d_not_22
                   (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8 v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.tryParseTypeVar
d_tryParseTypeVar_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryParseTypeVar_20 v0 v1
  = let v2
          = coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 in
    coe
      (case coe v2 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         (:) v3 v4
           -> let v5
                    = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                        (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v3)
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d_not_22
                           (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8 v3)) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe MAlonzo.Code.Once.Type.C_TVar_56 (coe v0)) (coe v1))
                   else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeAtom
d_parseTypeAtom_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAtom_38 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> let v5 = d_tryParseTypeVar_20 (coe v4) (coe v2) in
                     coe
                       (case coe v4 of
                          l | (==) l ("Buffer" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Buffer_54) (coe v2))
                          l | (==) l ("Eff" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Once.Parser.Core.du__'62''62''61'__22
                                (coe d_parseTypeAtom_38)
                                (coe
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Core.du__'62''62''61'__22
                                        (coe d_parseTypeAtom_38)
                                        (coe
                                           (\ v7 ->
                                              coe
                                                MAlonzo.Code.Once.Parser.Core.du_return_12
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_Eff_44 (coe v6)
                                                   (coe v7))))))
                                (coe v2)
                          l | (==) l ("Fix" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Once.Parser.Core.du__'62''62''61'__22
                                (coe d_parseTypeAtom_38)
                                (coe
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Core.du_return_12
                                        (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v6))))
                                (coe v2)
                          l | (==) l ("Float" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Float_50) (coe v2))
                          l | (==) l ("IO" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Once.Parser.Core.du__'62''62''61'__22
                                (coe d_parseTypeAtom_38)
                                (coe
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Core.du_return_12
                                        (coe
                                           MAlonzo.Code.Once.Type.C_Eff_44
                                           (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v6))))
                                (coe v2)
                          l | (==) l ("Int" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Int_48) (coe v2))
                          l | (==) l ("String" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Str_52) (coe v2))
                          l | (==) l ("Unit" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v2))
                          l | (==) l ("Void" :: Data.Text.Text) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v2))
                          _ -> coe v5)
                MAlonzo.Code.Once.Parser.Token.C_TLParen_14
                  -> coe
                       MAlonzo.Code.Once.Parser.Core.du__'62''62''61'__22
                       (coe d_parseType_40)
                       (coe
                          (\ v4 ->
                             coe
                               MAlonzo.Code.Once.Parser.Core.du__'62''62'__54
                               (coe
                                  MAlonzo.Code.Once.Parser.Core.d_expect_162
                                  (coe MAlonzo.Code.Once.Parser.Token.C_TRParen_16))
                               (coe MAlonzo.Code.Once.Parser.Core.du_return_12 (coe v4))))
                       (coe v2)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Type.parseType
d_parseType_40 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseType_40 v0
  = let v1 = d_parseTypeAtom_38 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5 = d_parseTypeProdTail_84 (coe v3) (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> let v9 = d_parseTypeSumTail_124 (coe v7) (coe v8) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                             -> case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                    -> coe d_parseArrowTail_160 (coe v11) (coe v12)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> coe d_parseArrowTail_160 (coe v7) (coe v8)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> let v5 = d_parseTypeSumTail_124 (coe v3) (coe v4) in
                            coe
                              (case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> coe d_parseArrowTail_160 (coe v7) (coe v8)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                                -> coe d_parseArrowTail_160 (coe v3) (coe v4)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeSum
d_parseTypeSum_42 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSum_42 v0
  = let v1 = d_parseTypeAtom_38 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5 = d_parseTypeProdTail_84 (coe v3) (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe d_parseTypeSumTail_124 (coe v7) (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> coe d_parseTypeSumTail_124 (coe v3) (coe v4)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseTypeProd
d_parseTypeProd_44 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProd_44 v0
  = let v1 = d_parseTypeAtom_38 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parseTypeProdTail_84 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.tryProdCont
d_tryProdCont_80 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryProdCont_80 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TStar_44
                  -> coe d_parseTypeAtom_38 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Type.parseTypeProdTail
d_parseTypeProdTail_84 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeProdTail_84 v0 v1
  = let v2 = d_tryProdCont_80 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       d_parseTypeProdTail_84
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v4)) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.trySumCont
d_trySumCont_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trySumCont_120 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TPlus_40
                  -> coe d_parseTypeProd_44 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Type.parseTypeSumTail
d_parseTypeSumTail_124 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeSumTail_124 v0 v1
  = let v2 = d_trySumCont_120 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       d_parseTypeSumTail_124
                       (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v4)) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Type.parseArrowTail
d_parseArrowTail_160 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseArrowTail_160 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TArrow_26
                  -> let v5 = d_parseType_40 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v0)
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                                           (coe v8))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
