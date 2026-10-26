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

module MAlonzo.Code.Once.Format.Comment where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Format.Doc
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Format.Comment.is
d_is_6 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_is_6 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe v1))
-- Once.Format.Comment.allDash
d_allDash_12 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allDash_12 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is_6 (coe v1) (coe '-')) (coe d_allDash_12 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.listItem
d_listItem_18 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_listItem_18 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                     (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                     (coe du_digitsThen_30 (coe v2)) in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v4 of
                       ' '
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_is_6 (coe v1) (coe '*'))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe d_is_6 (coe v1) (coe '-'))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                    (coe d_is_6 (coe v1) (coe '+'))
                                    (coe d_is_6 (coe v1) (coe '\8226'))))
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.digitsThen
d_digitsThen_30 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_digitsThen_30 ~v0 ~v1 v2 = du_digitsThen_30 v2
du_digitsThen_30 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
du_digitsThen_30 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                     (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                     (coe du_digitsThen_30 (coe v2)) in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v4 of
                       ' '
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_is_6 (coe v1) (coe '.')) (coe d_is_6 (coe v1) (coe ')'))
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.words
d_words_38 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_words_38 v0
  = coe
      du_go_54 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Comment._.emitW
d_emitW_46 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emitW_46 ~v0 v1 v2 = du_emitW_46 v1 v2
du_emitW_46 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_emitW_46 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0))
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.go
d_go_54 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_go_54 ~v0 v1 v2 = du_go_54 v1 v2
du_go_54 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_go_54 v0 v1
  = case coe v0 of
      [] -> coe du_emitW_46 (coe v1) (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_is_6 (coe v2) (coe ' ')) (coe d_is_6 (coe v2) (coe '\t')))
             (coe
                du_emitW_46 (coe v1)
                (coe
                   du_go_54 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                du_go_54 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.CLine
d_CLine_64 = ()
data T_CLine_64
  = C_prose_66 [MAlonzo.Code.Agda.Builtin.String.T_String_6] |
    C_verbatim_68 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Format.Comment.classify
d_classify_70 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CLine_64
d_classify_70 v0
  = coe
      d_go_78 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Comment._.go
d_go_78 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_64
d_go_78 v0 v1
  = let v2 = coe C_verbatim_68 (coe v0) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                '-'
                  -> case coe v4 of
                       (:) v5 v6
                         -> case coe v5 of
                              '-'
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                     (coe d_allDash_12 (coe v6)) (coe C_verbatim_68 (coe v0))
                                     (coe du_after_86 (coe v0) (coe v6))
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Comment._._.after
d_after_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_64
d_after_86 v0 ~v1 v2 = du_after_86 v0 v2
du_after_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_64
du_after_86 v0 v1
  = let v2 = coe C_prose_66 (coe d_words_38 (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                ' '
                  -> let v5
                           = coe
                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                               (coe d_listItem_18 (coe v4)) (coe C_verbatim_68 (coe v0))
                               (coe C_prose_66 (coe d_words_38 (coe v4))) in
                     coe
                       (case coe v4 of
                          [] -> coe C_verbatim_68 (coe ("--" :: Data.Text.Text))
                          (:) v6 v7
                            -> case coe v6 of
                                 ' ' -> coe C_verbatim_68 (coe v0)
                                 _ -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Comment.commentRun
d_commentRun_94 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_commentRun_94 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> let v3
                 = d_go_78
                     (coe v1)
                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1) in
           coe
             (case coe v3 of
                C_prose_66 v4
                  -> coe
                       MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                       (coe MAlonzo.Code.Once.Format.Doc.C_para_20 (coe v4))
                       (coe
                          MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                          (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
                          (coe d_commentRun_94 (coe v2)))
                C_verbatim_68 v4
                  -> coe
                       MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                       (coe MAlonzo.Code.Once.Format.Doc.C_cmt_18 (coe v4))
                       (coe
                          MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                          (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
                          (coe d_commentRun_94 (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.eolText
d_eolText_116 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_eolText_116 v0
  = coe
      d_go_124 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Comment._.go
d_go_124 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_go_124 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v2 of
             '-'
               -> case coe v3 of
                    (:) v4 v5
                      -> case coe v4 of
                           '-'
                             -> let v6
                                      = coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                          (coe d_allDash_12 (coe v5)) (coe v0)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("-- " :: Data.Text.Text)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                                v5)) in
                                coe
                                  (case coe v5 of
                                     [] -> coe v0
                                     (:) v7 v8
                                       -> case coe v7 of
                                            ' ' -> coe v0
                                            _ -> coe v6
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
