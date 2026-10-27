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
-- Once.Format.Comment.blankish
d_blankish_38 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_blankish_38 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe d_is_6 (coe v0) (coe ' '))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe d_is_6 (coe v0) (coe '\t')) (coe d_is_6 (coe v0) (coe '\r')))
-- Once.Format.Comment.words
d_words_42 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_words_42 v0
  = coe
      du_go_58 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Comment._.emitW
d_emitW_50 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emitW_50 ~v0 v1 v2 = du_emitW_50 v1 v2
du_emitW_50 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_emitW_50 v0 v1
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
d_go_58 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_go_58 ~v0 v1 v2 = du_go_58 v1 v2
du_go_58 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_go_58 v0 v1
  = case coe v0 of
      [] -> coe du_emitW_50 (coe v1) (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_blankish_38 (coe v2))
             (coe
                du_emitW_50 (coe v1)
                (coe
                   du_go_58 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                du_go_58 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.dropBlanks
d_dropBlanks_68 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_dropBlanks_68 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_blankish_38 (coe v1)) (coe d_dropBlanks_68 (coe v2))
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.strip
d_strip_74 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_strip_74 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_dropBlanks_68
         (coe
            MAlonzo.Code.Data.List.Base.du_reverse_444
            (d_dropBlanks_68 (coe v0))))
-- Once.Format.Comment.linesOf
d_linesOf_78 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_linesOf_78 v0
  = coe
      du_go_86 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Comment._.go
d_go_86 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_go_86 ~v0 v1 v2 = du_go_86 v1 v2
du_go_86 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
du_go_86 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1) (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_is_6 (coe v2) (coe '\n'))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1)
                (coe
                   du_go_86 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                du_go_86 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.inside
d_inside_96 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_inside_96 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v1 of
             '{'
               -> case coe v2 of
                    (:) v3 v4
                      -> case coe v3 of
                           '-'
                             -> coe
                                  du_unclose_104 (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v4)
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Comment._.unclose
d_unclose_104 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_unclose_104 ~v0 v1 = du_unclose_104 v1
du_unclose_104 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_unclose_104 v0
  = let v1 = coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                '}'
                  -> case coe v3 of
                       (:) v4 v5
                         -> case coe v4 of
                              '-' -> coe MAlonzo.Code.Data.List.Base.du_reverse_444 v5
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Comment.isBlock
d_isBlock_112 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isBlock_112 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                '{'
                  -> case coe v3 of
                       (:) v4 v5
                         -> case coe v4 of
                              '-' -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Comment.asLine
d_asLine_114 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asLine_114 v0
  = case coe v0 of
      [] -> coe ("--" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ') (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.trimLines
d_trimLines_118 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_trimLines_118 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (coe
         du_dropEmpty_126
         (coe
            MAlonzo.Code.Data.List.Base.du_reverse_444
            (coe du_dropEmpty_126 (coe v0))))
-- Once.Format.Comment._.dropEmpty
d_dropEmpty_126 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_dropEmpty_126 ~v0 v1 = du_dropEmpty_126 v1
du_dropEmpty_126 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
du_dropEmpty_126 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v1 of
             [] -> coe du_dropEmpty_126 (coe v2)
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Comment.atLeastOne
d_atLeastOne_132 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_atLeastOne_132 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe ("--" :: Data.Text.Text)) (coe v0)
      (:) v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.commentLines
d_commentLines_136 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_commentLines_136 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         d_isBlock_112
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
      (coe
         d_atLeastOne_132
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe (\ v1 -> d_asLine_114 (coe d_strip_74 (coe v1))))
            (coe
               d_trimLines_118
               (coe
                  d_linesOf_78
                  (coe
                     d_inside_96
                     (coe
                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Format.Comment.CLine
d_CLine_142 = ()
data T_CLine_142
  = C_prose_144 [MAlonzo.Code.Agda.Builtin.String.T_String_6] |
    C_verbatim_146 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Format.Comment.classify
d_classify_148 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CLine_142
d_classify_148 v0
  = coe
      d_go_156 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Comment._.go
d_go_156 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_142
d_go_156 v0 v1
  = let v2 = coe C_verbatim_146 (coe v0) in
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
                                     (coe d_allDash_12 (coe v6)) (coe C_verbatim_146 (coe v0))
                                     (coe du_after_164 (coe v0) (coe v6))
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Comment._._.after
d_after_164 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_142
d_after_164 v0 ~v1 v2 = du_after_164 v0 v2
du_after_164 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_142
du_after_164 v0 v1
  = let v2 = coe C_prose_144 (coe d_words_42 (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                ' '
                  -> let v5
                           = coe
                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                               (coe d_listItem_18 (coe v4)) (coe C_verbatim_146 (coe v0))
                               (coe C_prose_144 (coe d_words_42 (coe v4))) in
                     coe
                       (case coe v4 of
                          [] -> coe C_verbatim_146 (coe ("--" :: Data.Text.Text))
                          (:) v6 v7
                            -> case coe v6 of
                                 ' ' -> coe C_verbatim_146 (coe v0)
                                 _ -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Comment.commentLinesDoc
d_commentLinesDoc_172 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_commentLinesDoc_172 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> let v3
                 = d_go_156
                     (coe v1)
                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1) in
           coe
             (case coe v3 of
                C_prose_144 v4
                  -> coe
                       MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                       (coe MAlonzo.Code.Once.Format.Doc.C_para_20 (coe v4))
                       (coe
                          MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                          (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
                          (coe d_commentLinesDoc_172 (coe v2)))
                C_verbatim_146 v4
                  -> coe
                       MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                       (coe MAlonzo.Code.Once.Format.Doc.C_cmt_18 (coe v4))
                       (coe
                          MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                          (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
                          (coe d_commentLinesDoc_172 (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.commentRun
d_commentRun_174 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_commentRun_174 v0
  = coe
      d_commentLinesDoc_172
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246
         (coe d_commentLines_136) (coe v0))
-- Once.Format.Comment.eolText
d_eolText_198 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_eolText_198 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         d_isBlock_112
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
      (coe
         d_asLine_114
         (coe
            d_strip_74
            (coe
               MAlonzo.Code.Data.List.Base.du_concatMap_246
               (coe
                  (\ v1 ->
                     coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe d_is_6 (coe v1) (coe '\n'))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
               (coe
                  d_inside_96
                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)))))
      (coe
         d_go_206 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Format.Comment._.go
d_go_206 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_go_206 v0 v1
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
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("-- " :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                             v5) in
                                coe
                                  (case coe v5 of
                                     [] -> coe v0
                                     (:) v7 v8
                                       -> case coe v7 of
                                            ' ' -> coe v0
                                            '-' -> coe v0
                                            _ -> coe v6
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
