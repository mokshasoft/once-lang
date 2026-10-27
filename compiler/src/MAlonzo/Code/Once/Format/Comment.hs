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
import qualified MAlonzo.Code.Once.Format.Doc
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Format.Comment._.is
d_is_10 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_is_10 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe v1))
-- Once.Format.Comment._.allDash
d_allDash_16 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allDash_16 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_is_10 (coe v1) (coe '-')) (coe d_allDash_16 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.listItem
d_listItem_22 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_listItem_22 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                     (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                     (coe du_digitsThen_34 (coe v2)) in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v4 of
                       ' '
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_is_10 (coe v1) (coe '*'))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe d_is_10 (coe v1) (coe '-'))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                    (coe d_is_10 (coe v1) (coe '+'))
                                    (coe d_is_10 (coe v1) (coe '\8226'))))
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._._.digitsThen
d_digitsThen_34 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_digitsThen_34 ~v0 ~v1 v2 = du_digitsThen_34 v2
du_digitsThen_34 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
du_digitsThen_34 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                     (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10 v1)
                     (coe du_digitsThen_34 (coe v2)) in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v4 of
                       ' '
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_is_10 (coe v1) (coe '.')) (coe d_is_10 (coe v1) (coe ')'))
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.blankish
d_blankish_42 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_blankish_42 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe d_is_10 (coe v0) (coe ' '))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe d_is_10 (coe v0) (coe '\t'))
         (coe d_is_10 (coe v0) (coe '\r')))
-- Once.Format.Comment._.emitW
d_emitW_46 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emitW_46 v0 v1
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
-- Once.Format.Comment._.wordsGo
d_wordsGo_54 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_wordsGo_54 v0 v1
  = case coe v0 of
      [] -> coe d_emitW_46 (coe v1) (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_blankish_42 (coe v2))
             (coe
                d_emitW_46 (coe v1)
                (coe
                   d_wordsGo_54 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                d_wordsGo_54 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.words
d_words_64 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_words_64 v0
  = coe
      d_wordsGo_54 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Comment._.dropBlanks
d_dropBlanks_68 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_dropBlanks_68 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_blankish_42 (coe v1)) (coe d_dropBlanks_68 (coe v2))
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.strip
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
-- Once.Format.Comment._.linesGo
d_linesGo_78 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_linesGo_78 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1) (coe v0)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_is_10 (coe v2) (coe '\n'))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1)
                (coe
                   d_linesGo_78 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                d_linesGo_78 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment._.linesOf
d_linesOf_88 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_linesOf_88 v0
  = coe
      d_linesGo_78 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Comment._.inside
d_inside_92 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_inside_92 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v1 of
             '{'
               -> case coe v2 of
                    (:) v3 v4
                      -> case coe v3 of
                           '-'
                             -> coe
                                  du_unclose_100 (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v4)
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Comment._._.unclose
d_unclose_100 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_unclose_100 ~v0 v1 = du_unclose_100 v1
du_unclose_100 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_unclose_100 v0
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
-- Once.Format.Comment._.isBlock
d_isBlock_108 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isBlock_108 v0
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
-- Once.Format.Comment._.asLine
d_asLine_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asLine_110 v0
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
-- Once.Format.Comment._.dropEmpty
d_dropEmpty_114 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_dropEmpty_114 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v1 of
             [] -> coe d_dropEmpty_114 (coe v2)
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Comment._.trimLines
d_trimLines_120 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]]
d_trimLines_120 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_dropEmpty_114
         (coe
            MAlonzo.Code.Data.List.Base.du_reverse_444
            (d_dropEmpty_114 (coe v0))))
-- Once.Format.Comment.atLeastOne
d_atLeastOne_124 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_atLeastOne_124 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe ("--" :: Data.Text.Text)) (coe v0)
      (:) v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.commentLines
d_commentLines_128 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_commentLines_128 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         d_isBlock_108
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
      (coe
         d_atLeastOne_124
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe (\ v1 -> d_asLine_110 (coe d_strip_74 (coe v1))))
            (coe
               d_trimLines_120
               (coe
                  d_linesOf_88
                  (coe
                     d_inside_92
                     (coe
                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Format.Comment.CLine
d_CLine_134 = ()
data T_CLine_134
  = C_prose_136 [MAlonzo.Code.Agda.Builtin.String.T_String_6] |
    C_verbatim_138 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Format.Comment.afterBlank
d_afterBlank_140 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_134
d_afterBlank_140 v0 v1
  = case coe v1 of
      [] -> coe C_verbatim_138 (coe ("--" :: Data.Text.Text))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_is_10 (coe v2) (coe ' ')) (coe C_verbatim_138 (coe v0))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_listItem_22 (coe v1)) (coe C_verbatim_138 (coe v0))
                (coe C_prose_136 (coe d_words_64 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.afterDashes
d_afterDashes_150 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_134
d_afterDashes_150 v0 v1
  = case coe v1 of
      [] -> coe C_prose_136 (coe v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_is_10 (coe v2) (coe ' '))
             (coe d_afterBlank_140 (coe v0) (coe v3))
             (coe C_prose_136 (coe d_words_64 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.classifyChars
d_classifyChars_160 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> T_CLine_134
d_classifyChars_160 v0 v1
  = let v2 = coe C_verbatim_138 (coe v0) in
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
                                     (coe d_allDash_16 (coe v6)) (coe C_verbatim_138 (coe v0))
                                     (coe d_afterDashes_150 (coe v0) (coe v6))
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Comment.classify
d_classify_168 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CLine_134
d_classify_168 v0
  = coe
      d_classifyChars_160 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Comment.commentLinesDoc
d_commentLinesDoc_172 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_commentLinesDoc_172 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
             (coe d_lineDoc_178 (coe d_classify_168 (coe v1)))
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
                (coe d_commentLinesDoc_172 (coe v2)))
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
         (coe d_commentLines_128) (coe v0))
-- Once.Format.Comment.lineDoc
d_lineDoc_178 ::
  T_CLine_134 -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_lineDoc_178 v0
  = case coe v0 of
      C_prose_136 v1
        -> coe MAlonzo.Code.Once.Format.Doc.C_para_20 (coe v1)
      C_verbatim_138 v1
        -> coe MAlonzo.Code.Once.Format.Doc.C_cmt_18 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Comment.eolChars
d_eolChars_188 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_eolChars_188 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v2 of
             '-'
               -> case coe v3 of
                    (:) v4 v5
                      -> case coe v4 of
                           '-'
                             -> case coe v5 of
                                  [] -> coe v0
                                  (:) v6 v7
                                    -> coe
                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                         (coe
                                            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                            (coe d_is_10 (coe v6) (coe ' '))
                                            (coe d_is_10 (coe v6) (coe '-')))
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe '-')
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe '-')
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ' ') (coe v5)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Comment.eolText
d_eolText_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_eolText_200 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         d_isBlock_108
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
      (coe
         d_asLine_110
         (coe
            d_strip_74
            (coe
               MAlonzo.Code.Data.List.Base.du_concatMap_246
               (coe
                  (\ v1 ->
                     coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe d_is_10 (coe v1) (coe '\n'))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
               (coe
                  d_inside_92
                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)))))
      (coe
         d_eolChars_188 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
