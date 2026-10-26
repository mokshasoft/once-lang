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

module MAlonzo.Code.Once.Format.Print where

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
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Format.Doc
import qualified MAlonzo.Code.Once.Format.Lex
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Format.Print.Note
d_Note_6 = ()
data T_Note_6
  = C_note'45'comment_8 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_note'45'blank_10
-- Once.Format.Print.Notes
d_Notes_12 = ()
data T_Notes_12
  = C_notes_26 [T_Note_6]
               [MAlonzo.Code.Agda.Builtin.String.T_String_6]
               [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Format.Print.Notes.top
d_top_20 :: T_Notes_12 -> [T_Note_6]
d_top_20 v0
  = case coe v0 of
      C_notes_26 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.Notes.inner
d_inner_22 ::
  T_Notes_12 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_inner_22 v0
  = case coe v0 of
      C_notes_26 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.Notes.after
d_after_24 ::
  T_Notes_12 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_after_24 v0
  = case coe v0 of
      C_notes_26 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.noNotes
d_noNotes_28 :: T_Notes_12
d_noNotes_28
  = coe
      C_notes_26 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Format.Print.Trivia
d_Trivia_30 :: ()
d_Trivia_30 = erased
-- Once.Format.Print.isAnchor
d_isAnchor_32 :: MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool
d_isAnchor_32 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TWord_8 v2
           -> coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe
                   MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
                   (coe ("compose" :: Data.Text.Text)))
         MAlonzo.Code.Once.Parser.Token.C_TInt_10 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v2 v3 v4 v5
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.trimEnd
d_trimEnd_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_trimEnd_36 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_reverse_444
         (coe
            du_dropBlanks_44
            (coe
               MAlonzo.Code.Data.List.Base.du_reverse_444
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))))
-- Once.Format.Print._.dropBlanks
d_dropBlanks_44 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_dropBlanks_44 ~v0 v1 = du_dropBlanks_44 v1
du_dropBlanks_44 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_dropBlanks_44 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe ' ')))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                      (coe
                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                         (coe '\t')))
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                      (coe
                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                         (coe '\r')))))
             (coe du_dropBlanks_44 (coe v2)) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.addTo
d_addTo_50 ::
  Integer ->
  (T_Notes_12 -> T_Notes_12) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_addTo_50 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe v1 d_noNotes_28))
             (coe v2)
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v0) (coe v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v1 v6))
                       (coe v4))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                       (coe d_addTo_50 (coe v0) (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.addTop
d_addTop_66 :: T_Note_6 -> T_Notes_12 -> T_Notes_12
d_addTop_66 v0 v1
  = case coe v1 of
      C_notes_26 v2 v3 v4
        -> coe
             C_notes_26
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.addInner
d_addInner_76 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Notes_12 -> T_Notes_12
d_addInner_76 v0 v1
  = case coe v1 of
      C_notes_26 v2 v3 v4
        -> coe
             C_notes_26 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.addAfter
d_addAfter_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Notes_12 -> T_Notes_12
d_addAfter_86 v0 v1
  = case coe v1 of
      C_notes_26 v2 v3 v4
        -> coe
             C_notes_26 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.Line
d_Line_96 = ()
data T_Line_96
  = C_line'45'empty_98 | C_line'45'code_100 |
    C_line'45'text_102 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Format.Print.Held
d_Held_104 = ()
data T_Held_104
  = C_held'45'comment_106 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          Bool |
    C_held'45'blank_108
-- Once.Format.Print.W
d_W_110 = ()
data T_W_110
  = C_w_132 Integer T_Line_96 [T_Held_104] Integer
            [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Format.Print.W.k
d_k_122 :: T_W_110 -> Integer
d_k_122 v0
  = case coe v0 of
      C_w_132 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.ln
d_ln_124 :: T_W_110 -> T_Line_96
d_ln_124 v0
  = case coe v0 of
      C_w_132 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.held
d_held_126 :: T_W_110 -> [T_Held_104]
d_held_126 v0
  = case coe v0 of
      C_w_132 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.breaks
d_breaks_128 :: T_W_110 -> Integer
d_breaks_128 v0
  = case coe v0 of
      C_w_132 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.acc
d_acc_130 :: T_W_110 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_acc_130 v0
  = case coe v0 of
      C_w_132 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.go
d_go_150 ::
  Integer ->
  T_Line_96 ->
  [T_Held_104] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Held_104] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_150 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_go_150 v0 v5 v6
du_go_150 ::
  Integer ->
  [T_Held_104] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_150 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             C_held'45'comment_106 v5 v6
               -> if coe v6
                    then coe
                           du_go_150 (coe v0) (coe v4)
                           (coe
                              d_addTo_50 (coe v0)
                              (coe d_addTop_66 (coe C_note'45'comment_8 (coe v5))) (coe v2))
                    else coe
                           du_go_150 (coe v0) (coe v4)
                           (coe d_addTo_50 (coe v0) (coe d_addInner_76 (coe v5)) (coe v2))
             C_held'45'blank_108
               -> coe
                    du_go_150 (coe v0) (coe v4)
                    (coe
                       d_addTo_50 (coe v0) (coe d_addTop_66 (coe C_note'45'blank_10))
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.blankBefore
d_blankBefore_170 :: Integer -> [T_Held_104] -> [T_Held_104]
d_blankBefore_170 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         ltInt (coe (2 :: Integer))
         (coe addInt (coe (1 :: Integer)) (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe C_held'45'blank_108)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe v1)
-- Once.Format.Print.lineEnd
d_lineEnd_176 :: Bool -> T_W_110 -> T_W_110
d_lineEnd_176 v0 v1
  = case coe v1 of
      C_w_132 v2 v3 v4 v5 v6
        -> case coe v3 of
             C_line'45'empty_98
               -> coe
                    C_w_132 (coe v2) (coe v3) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             C_line'45'code_100
               -> coe
                    C_w_132 (coe v2) (coe C_line'45'empty_98) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             C_line'45'text_102 v7
               -> coe
                    C_w_132 (coe v2) (coe C_line'45'empty_98)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_held'45'comment_106 (coe v7) (coe v0))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                    (coe (1 :: Integer)) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.isLineEnd
d_isLineEnd_210 :: MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool
d_isLineEnd_210 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TNewline_74
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Parser.Token.C_TEOF_76
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.pending
d_pending_212 :: T_Line_96 -> [T_Held_104] -> [T_Held_104]
d_pending_212 v0 v1
  = case coe v0 of
      C_line'45'empty_98 -> coe v1
      C_line'45'code_100 -> coe v1
      C_line'45'text_102 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   C_held'45'comment_106 (coe v2)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.stepTok
d_stepTok_222 ::
  T_W_110 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool -> T_W_110
d_stepTok_222 v0 v1 v2
  = if coe v2
      then coe d_lineEnd_176 (coe v2) (coe v0)
      else (case coe v0 of
              C_w_132 v3 v4 v5 v6 v7
                -> let v8
                         = coe
                             du_go_150 (coe v3)
                             (coe
                                d_pending_212 (coe v4) (coe d_blankBefore_170 (coe v6) (coe v5)))
                             (coe v7) in
                   coe
                     (coe
                        C_w_132
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe d_isAnchor_32 (coe v1))
                           (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v3))
                        (coe C_line'45'code_100)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                        (coe (0 :: Integer)) (coe v8))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print.stepComment
d_stepComment_260 ::
  T_W_110 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_W_110
d_stepComment_260 v0 v1
  = case coe v0 of
      C_w_132 v2 v3 v4 v5 v6
        -> case coe v3 of
             C_line'45'empty_98
               -> coe
                    C_w_132 (coe v2) (coe C_line'45'text_102 (coe v1))
                    (coe d_blankBefore_170 (coe v5) (coe v4)) (coe (0 :: Integer))
                    (coe v6)
             C_line'45'code_100
               -> coe
                    C_w_132 (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe eqInt (coe v2) (coe (0 :: Integer)))
                       (coe
                          d_addTo_50 (coe (0 :: Integer))
                          (coe d_addTop_66 (coe C_note'45'comment_8 (coe v1))) (coe v6))
                       (coe
                          d_addTo_50
                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 (1 :: Integer))
                          (coe d_addAfter_86 (coe v1)) (coe v6)))
             C_line'45'text_102 v7
               -> coe
                    C_w_132 (coe v2)
                    (coe
                       C_line'45'text_102
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v7
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (" " :: Data.Text.Text) v1)))
                    (coe v4) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.step
d_step_294 ::
  T_W_110 -> MAlonzo.Code.Once.Format.Lex.T_Item_6 -> T_W_110
d_step_294 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Format.Lex.C_tok_8 v2
        -> coe
             d_stepTok_222 (coe v0) (coe v2) (coe d_isLineEnd_210 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_comment_10 v2
        -> coe d_stepComment_260 (coe v0) (coe d_trimEnd_36 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_cont_12
        -> coe
             d_lineEnd_176 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.trivia
d_trivia_306 ::
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_trivia_306 v0
  = coe
      du_finish_328
      (coe
         du_foldl'8242'_314 (coe d_step_294)
         (coe
            C_w_132 (coe (0 :: Integer)) (coe C_line'45'empty_98)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe v0))
-- Once.Format.Print._.foldl′
d_foldl'8242'_314 ::
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  (T_W_110 -> MAlonzo.Code.Once.Format.Lex.T_Item_6 -> T_W_110) ->
  T_W_110 -> [MAlonzo.Code.Once.Format.Lex.T_Item_6] -> T_W_110
d_foldl'8242'_314 ~v0 v1 v2 v3 = du_foldl'8242'_314 v1 v2 v3
du_foldl'8242'_314 ::
  (T_W_110 -> MAlonzo.Code.Once.Format.Lex.T_Item_6 -> T_W_110) ->
  T_W_110 -> [MAlonzo.Code.Once.Format.Lex.T_Item_6] -> T_W_110
du_foldl'8242'_314 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe du_foldl'8242'_314 (coe v0) (coe v0 v1 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.finish
d_finish_328 ::
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  T_W_110 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_finish_328 ~v0 v1 = du_finish_328 v1
du_finish_328 ::
  T_W_110 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_finish_328 v0
  = coe
      du_go_150
      (coe
         d_k_122
         (coe
            d_lineEnd_176 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe v0)))
      (coe
         d_held_126
         (coe
            d_lineEnd_176 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe v0)))
      (coe
         d_acc_130
         (coe
            d_lineEnd_176 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe v0)))
-- Once.Format.Print.lookupNotes
d_lookupNotes_340 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Notes_12
d_lookupNotes_340 v0 v1
  = case coe v1 of
      [] -> coe d_noNotes_28
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v0) (coe v4)) (coe v5)
                    (coe d_lookupNotes_340 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.P
d_P_352 :: () -> ()
d_P_352 = erased
-- Once.Format.Print.pure′
d_pure'8242'_358 ::
  () ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pure'8242'_358 ~v0 v1 ~v2 v3 = du_pure'8242'_358 v1 v3
du_pure'8242'_358 ::
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pure'8242'_358 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Format.Print._>>=′_
d__'62''62''61''8242'__368 ::
  () ->
  () ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61''8242'__368 ~v0 ~v1 v2 v3 v4 v5
  = du__'62''62''61''8242'__368 v2 v3 v4 v5
du__'62''62''61''8242'__368 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62''61''8242'__368 v0 v1 v2 v3
  = let v4 = coe v0 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe v1 v5 v2 v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print._⊕ᵈ_
d__'8853''7496'__394 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8853''7496'__394 v0 v1
  = coe
      du__'62''62''61''8242'__368 (coe v0)
      (coe
         (\ v2 ->
            coe
              du__'62''62''61''8242'__368 (coe v1)
              (coe
                 (\ v3 v4 v5 ->
                    coe
                      du_pure'8242'_358
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C__'60''62'__24 (coe v2) (coe v3))
                      v5))))
-- Once.Format.Print.txt
d_txt_404 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_txt_404 v0 v1 v2
  = coe
      du_pure'8242'_358
      (coe MAlonzo.Code.Once.Format.Doc.C_text_14 (coe v0)) v2
-- Once.Format.Print.anchor
d_anchor_408 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anchor_408 v0 v1 v2
  = let v3 = d_lookupNotes_340 (coe v2) (coe v1) in
    coe
      (case coe v3 of
         C_notes_26 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216
                      (coe
                         (\ v7 v8 ->
                            coe
                              MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                              (coe MAlonzo.Code.Once.Format.Doc.C_newline_18)
                              (coe
                                 MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                                 (coe MAlonzo.Code.Once.Format.Doc.C_text_14 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                                    (coe MAlonzo.Code.Once.Format.Doc.C_newline_18) (coe v8)))))
                      (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) (coe v5))
                   (coe
                      MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                      (coe MAlonzo.Code.Once.Format.Doc.C_text_14 (coe v0))
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe
                            (\ v7 ->
                               coe
                                 MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                                 (coe MAlonzo.Code.Once.Format.Doc.C_eol_22 (coe v7))))
                         (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) (coe v6))))
                (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print.word
d_word_438 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_word_438 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v0)
         (coe ("compose" :: Data.Text.Text)))
      (coe d_txt_404 (coe v0)) (coe d_anchor_408 (coe v0))
-- Once.Format.Print.topNotes
d_topNotes_442 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_topNotes_442 v0 v1 v2
  = coe
      du_go_458 (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
-- Once.Format.Print._.one
d_one_454 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Note_6 -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_one_454 ~v0 ~v1 ~v2 v3 = du_one_454 v3
du_one_454 :: T_Note_6 -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
du_one_454 v0
  = case coe v0 of
      C_note'45'comment_8 v1
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
             (coe MAlonzo.Code.Once.Format.Doc.C_text_14 (coe v1))
             (coe MAlonzo.Code.Once.Format.Doc.C_newline_18)
      C_note'45'blank_10 -> coe MAlonzo.Code.Once.Format.Doc.C_blank_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.go
d_go_458 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> Integer -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_go_458 ~v0 ~v1 v2 v3 v4 = du_go_458 v2 v3 v4
du_go_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> Integer -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
du_go_458 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                (coe
                   MAlonzo.Code.Data.List.Base.du_foldr_216
                   (coe
                      (\ v4 ->
                         coe
                           MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                           (coe du_one_454 (coe v4))))
                   (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
                   (coe d_top_20 (coe d_lookupNotes_340 (coe v1) (coe v0))))
                (coe
                   du_go_458 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                   (coe v3)))
-- Once.Format.Print.opChars
d_opChars_470 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_opChars_470
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '.')
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '+')
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '*')
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '/')
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '<')
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '>')
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '|')
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '&')
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '@')
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.Format.Print.isOpChar
d_isOpChar_472 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isOpChar_472 v0 = coe d_go_480 (coe v0) (coe d_opChars_470)
-- Once.Format.Print._.go
d_go_480 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_go_480 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe v2)))
             (coe d_go_480 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.allOp
d_allOp_486 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allOp_486 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_isOpChar_472 (coe v1)
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_isOpChar_472 (coe v1)) (coe d_allOp_486 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.spaceOp
d_spaceOp_494 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_spaceOp_494 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v2 of
             [] -> coe v0
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                          (coe
                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                             (coe '-')))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v3)
                                (coe '-')))
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v3)
                                (coe '>')))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
                          (coe d_spaceOp_494 (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                       (coe d_spaceOp_494 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.isOperator
d_isOperator_504 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isOperator_504 v0
  = coe
      d_allOp_486
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Print.name
d_name_508 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_name_508 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_isOperator_504 (coe v0))
      (coe
         d_txt_404
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("(" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (coe
                  MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                  (d_spaceOp_494
                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)))
               (")" :: Data.Text.Text))))
      (coe d_word_438 (coe v0))
-- Once.Format.Print.showInt
d_showInt_512 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInt_512 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0
      _ -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("-" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.Nat.Show.d_show_56
                (subInt (coe (0 :: Integer)) (coe v0)))
-- Once.Format.Print.showFloat
d_showFloat_518 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFloat_518 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("." :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe
               MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
               (coe
                  MAlonzo.Code.Data.List.Base.du_replicate_278
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                     (MAlonzo.Code.Data.String.Base.d_length_22
                        (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)))
                  (coe '0')))
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)))
-- Once.Format.Print.paren
d_paren_526 ::
  Bool ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_paren_526 v0 v1
  = if coe v0
      then coe
             d__'8853''7496'__394 (coe d_txt_404 (coe ("(" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__394 (coe v1)
                (coe d_txt_404 (coe (")" :: Data.Text.Text))))
      else coe v1
-- Once.Format.Print.grade
d_grade_532 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_grade_532 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe d_txt_404 (coe (" ^0 ->" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe d_txt_404 (coe (" ^1 ->" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe d_txt_404 (coe (" ->" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pty
d_pty_534 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pty_534 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe d_word_438 (coe ("Unit" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe d_word_438 (coe ("Void" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe d_word_438 (coe ("Int" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe d_word_438 (coe ("Float" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (2 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_pty_534 (coe (2 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" * " :: Data.Text.Text)))
                   (coe
                      d_pty_534 (coe (3 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (2 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_pty_534 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" + " :: Data.Text.Text)))
                   (coe
                      d_pty_534 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (1 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> coe
             d_paren_526 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_pty_534 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__394 (coe d_grade_532 (coe v4))
                   (coe
                      d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                      (coe
                         d_pty_534 (coe (0 :: Integer))
                         (coe
                            MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                            (coe ltInt (coe (0 :: Integer)) (coe v0)))
                         (coe v5)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("Act" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394
                      (coe
                         d_pty_534 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                         (coe
                            d_pty_534 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("Eff" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394
                      (coe
                         d_pty_534 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                         (coe
                            d_pty_534 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe
             d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("Mu" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe d_pfunArg_536 (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__394
                       (coe d_word_438 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                          (coe d_pfunArg_536 (coe v3))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__394
                       (coe d_word_438 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__394 (coe d_txt_404 (coe (" (" :: Data.Text.Text)))
                          (coe
                             d__'8853''7496'__394
                             (coe d_word_438 (coe ("Act" :: Data.Text.Text)))
                             (coe
                                d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                (coe
                                   d__'8853''7496'__394
                                   (coe d_pfun_538 (coe (0 :: Integer)) (coe v3))
                                   (coe d_txt_404 (coe (")" :: Data.Text.Text))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v3
        -> coe d_word_438 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pfunArg
d_pfunArg_536 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfunArg_536 v0
  = let v1
          = d__'8853''7496'__394
              (coe d_txt_404 (coe ("(" :: Data.Text.Text)))
              (coe
                 d__'8853''7496'__394 (coe d_pfun_538 (coe (0 :: Integer)) (coe v0))
                 (coe d_txt_404 (coe (")" :: Data.Text.Text)))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
           -> coe d_word_438 (coe ("Id" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.pfun
d_pfun_538 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfun_538 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v2
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_word_438 (coe ("K" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d_pty_534 (coe (3 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe d_word_438 (coe ("Id" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v2 v3
        -> coe
             d_paren_526 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_pfun_538 (coe (0 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" + " :: Data.Text.Text)))
                   (coe d_pfun_538 (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v2 v3
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_pfun_538 (coe (1 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" * " :: Data.Text.Text)))
                   (coe d_pfun_538 (coe (2 :: Integer)) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gty
d_gty_642 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gty_642 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe (\ v4 v5 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe d_word_438 (coe ("Unit" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe d_word_438 (coe ("Void" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (2 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_gty_642 (coe (2 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" * " :: Data.Text.Text)))
                   (coe
                      d_gty_642 (coe (3 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (2 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_gty_642 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" + " :: Data.Text.Text)))
                   (coe
                      d_gty_642 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (1 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                      -> case coe v8 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  d_paren_526 (coe ltInt (coe (0 :: Integer)) (coe v0))
                                  (coe
                                     d__'8853''7496'__394
                                     (coe
                                        d_gty_642 (coe (1 :: Integer))
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                                     (coe
                                        d__'8853''7496'__394 (coe d_grade_532 (coe v6))
                                        (coe
                                           d__'8853''7496'__394
                                           (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                           (coe
                                              d_gty_642 (coe (0 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                                                 (coe ltInt (coe (0 :: Integer)) (coe v0)))
                                              (coe v5)))))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe
                                  d_paren_526 (coe ltInt (coe (3 :: Integer)) (coe v0))
                                  (coe
                                     d__'8853''7496'__394
                                     (coe d_word_438 (coe ("Act" :: Data.Text.Text)))
                                     (coe
                                        d__'8853''7496'__394
                                        (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                        (coe
                                           d__'8853''7496'__394
                                           (coe
                                              d_gty_642 (coe (3 :: Integer))
                                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                              (coe v3))
                                           (coe
                                              d__'8853''7496'__394
                                              (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                              (coe
                                                 d_gty_642 (coe (3 :: Integer))
                                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                 (coe v5))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           d_paren_526 (coe ltInt (coe (3 :: Integer)) (coe v0))
                           (coe
                              d__'8853''7496'__394
                              (coe d_word_438 (coe ("Eff" :: Data.Text.Text)))
                              (coe
                                 d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                 (coe
                                    d__'8853''7496'__394
                                    (coe
                                       d_gty_642 (coe (3 :: Integer))
                                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                                    (coe
                                       d__'8853''7496'__394
                                       (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                       (coe
                                          d_gty_642 (coe (3 :: Integer))
                                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                          (coe v5))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3
        -> coe
             d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("Mu" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe d_gfunArg_644 (coe v3))))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__394
                       (coe d_word_438 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                          (coe d_gfunArg_644 (coe v3))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__394
                       (coe d_word_438 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__394 (coe d_txt_404 (coe (" (" :: Data.Text.Text)))
                          (coe
                             d__'8853''7496'__394
                             (coe d_word_438 (coe ("Act" :: Data.Text.Text)))
                             (coe
                                d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                (coe
                                   d__'8853''7496'__394
                                   (coe d_gfun_646 (coe (0 :: Integer)) (coe v3))
                                   (coe d_txt_404 (coe (")" :: Data.Text.Text))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe d_word_438 (coe ("Int" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe d_word_438 (coe ("Float" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gfunArg
d_gfunArg_644 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gfunArg_644 v0
  = let v1
          = d__'8853''7496'__394
              (coe d_txt_404 (coe ("(" :: Data.Text.Text)))
              (coe
                 d__'8853''7496'__394 (coe d_gfun_646 (coe (0 :: Integer)) (coe v0))
                 (coe d_txt_404 (coe (")" :: Data.Text.Text)))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Id_40
           -> coe d_word_438 (coe ("Id" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.gfun
d_gfun_646 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gfun_646 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_word_438 (coe ("K" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d_gty_642 (coe (3 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))))
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe d_word_438 (coe ("Id" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> coe
             d_paren_526 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_gfun_646 (coe (0 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" + " :: Data.Text.Text)))
                   (coe d_gfun_646 (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> coe
             d_paren_526 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394 (coe d_gfun_646 (coe (1 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" * " :: Data.Text.Text)))
                   (coe d_gfun_646 (coe (2 :: Integer)) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opText
d_opText_748 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_opText_748 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe ("+" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe ("-" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe ("*" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe ("/" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe ("%" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe ("<" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe ("<=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe (">" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe (">=" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe ("==" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe ("!=" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opLevel
d_opLevel_750 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Integer
d_opLevel_750 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe (2 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe (2 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe (3 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe (3 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe (3 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.spine
d_spine_752 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spine_752 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> let v4 = d_spine_752 (coe v2) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v1)
-- Once.Format.Print.lams
d_lams_772 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lams_772 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
           -> let v4 = d_lams_772 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v5))
                          (coe v6)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v1)
-- Once.Format.Print.startsNeg
d_startsNeg_792 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_startsNeg_792 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.isCompose
d_isCompose_794 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_isCompose_794 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v2
           -> coe
                MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
                (coe ("compose" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.headOf
d_headOf_798 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_headOf_798 v0
  = let v1 = coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3 -> coe v2
         _ -> coe v1)
-- Once.Format.Print.pex
d_pex_806 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pex_806 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
        -> coe d_name_508 (coe v3)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
        -> coe
             d__'8853''7496'__394 (coe d_word_438 (coe v3))
             (coe
                d__'8853''7496'__394 (coe d_txt_404 (coe ("@" :: Data.Text.Text)))
                (coe d_word_438 (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v4
               -> coe
                    d_word_438
                    (coe
                       MAlonzo.Code.Data.String.Base.d_intersperse_30
                       ("." :: Data.Text.Text) v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
        -> coe
             d_pcomp_808 (coe v0) (coe v3) (coe v4)
             (coe d_isCompose_794 (coe d_headOf_798 (coe v3)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
        -> coe
             d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plam_824 (coe v3) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
        -> coe
             d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plet_828 (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
        -> coe
             du__'62''62''61''8242'__368
             (coe
                d__'8853''7496'__394 (coe d_txt_404 (coe ("(" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394
                   (coe
                      d_pex_806 (coe (0 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                   (coe
                      d__'8853''7496'__394 (coe d_txt_404 (coe ("," :: Data.Text.Text)))
                      (coe
                         d__'8853''7496'__394
                         (\ v5 v6 ->
                            coe
                              du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v6)
                         (coe
                            d__'8853''7496'__394
                            (coe
                               d_pex_806 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                            (coe d_txt_404 (coe (")" :: Data.Text.Text))))))))
             (coe
                (\ v5 v6 v7 ->
                   coe
                     du_pure'8242'_358
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_28
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_26
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5)))
                     v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
        -> coe
             d_paren_526 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_pdes_834 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe d_txt_404 (coe ("()" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
        -> coe d_anchor_408 (coe d_showInt_512 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
        -> coe
             d_anchor_408 (coe d_showFloat_518 (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
        -> coe
             d__'8853''7496'__394 (coe d_txt_404 (coe ("(" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__394
                (coe
                   d_pex_806 (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__394
                   (coe d_txt_404 (coe (" : " :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394
                      (coe
                         d_gty_642 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                      (coe d_txt_404 (coe (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
        -> coe
             du__'62''62''61''8242'__368
             (coe
                d_paren_526 (coe ltInt (coe d_opLevel_750 (coe v3)) (coe v0))
                (coe
                   d_pbin_816 (coe d_opLevel_750 (coe v3)) (coe v3) (coe v4)
                   (coe v5)))
             (coe
                (\ v6 v7 v8 ->
                   coe
                     du_pure'8242'_358
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_28
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_26
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v6)))
                     v8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
        -> coe
             d_paren_526 (coe ltInt (coe (4 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__394
                (coe
                   d_txt_404
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe d_startsNeg_792 (coe v3)) (coe ("- " :: Data.Text.Text))
                      (coe ("-" :: Data.Text.Text))))
                (coe
                   d_pex_806 (coe (4 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pcomp
d_pcomp_808 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcomp_808 v0 v1 v2 v3
  = let v4
          = coe
              du__'62''62''61''8242'__368
              (coe
                 d_paren_526 (coe ltInt (coe (5 :: Integer)) (coe v0))
                 (coe
                    d__'8853''7496'__394 (coe d_pspine_820 (coe v1))
                    (coe
                       d__'8853''7496'__394
                       (\ v4 v5 ->
                          coe
                            du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v5)
                       (coe
                          d_pex_806 (coe (6 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))))
              (coe
                 (\ v4 v5 v6 ->
                    coe
                      du_pure'8242'_358
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C_group_28
                         (coe
                            MAlonzo.Code.Once.Format.Doc.C_nest_26
                            (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v4)))
                      v6)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                  -> coe d_pcompose_810 (coe v0) (coe v6) (coe v2)
                _ -> coe v4
         _ -> coe v4)
-- Once.Format.Print.pcompose
d_pcompose_810 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcompose_810 v0 v1 v2
  = coe
      du__'62''62''61''8242'__368
      (coe
         d_paren_526 (coe ltInt (coe (0 :: Integer)) (coe v0))
         (coe
            d__'8853''7496'__394 (coe d_pchainC_812 (coe v1))
            (coe
               d__'8853''7496'__394
               (coe
                  d__'8853''7496'__394
                  (\ v3 v4 ->
                     coe
                       du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v4)
                  (coe d_txt_404 (coe (". " :: Data.Text.Text))))
               (coe
                  d_pex_806 (coe (1 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_358
              (coe
                 MAlonzo.Code.Once.Format.Doc.C_group_28
                 (coe
                    MAlonzo.Code.Once.Format.Doc.C_nest_26
                    (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v3)))
              v5))
-- Once.Format.Print.pchainC
d_pchainC_812 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC_812 v0
  = let v1
          = d_pex_806
              (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pchainC'8242'_814 (coe v2) (coe v3)
                (coe d_isCompose_794 (coe d_headOf_798 (coe v2)))
         _ -> coe v1)
-- Once.Format.Print.pchainC′
d_pchainC'8242'_814 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC'8242'_814 v0 v1 v2
  = let v3
          = d_pcomp_808
              (coe (0 :: Integer)) (coe v0) (coe v1)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                  -> coe
                       d__'8853''7496'__394 (coe d_pchainC_812 (coe v5))
                       (coe
                          d__'8853''7496'__394
                          (coe
                             d__'8853''7496'__394
                             (\ v6 v7 ->
                                coe
                                  du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v7)
                             (coe d_txt_404 (coe (". " :: Data.Text.Text))))
                          (coe
                             d_pex_806 (coe (1 :: Integer))
                             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1)))
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.pbin
d_pbin_816 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pbin_816 v0 v1 v2 v3
  = coe
      d__'8853''7496'__394 (coe d_pleft_818 (coe v0) (coe v2))
      (coe
         d__'8853''7496'__394
         (\ v4 v5 ->
            coe
              du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v5)
         (coe
            d__'8853''7496'__394
            (coe
               d_txt_404
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (d_opText_748 (coe v1)) (" " :: Data.Text.Text)))
            (coe
               d_pex_806 (coe addInt (coe (1 :: Integer)) (coe v0))
               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))))
-- Once.Format.Print.pleft
d_pleft_818 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pleft_818 v0 v1
  = let v2
          = d_pex_806
              (coe v0) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe eqInt (coe v0) (coe d_opLevel_750 (coe v3)))
                   (coe ltInt (coe (1 :: Integer)) (coe v0)))
                (coe d_pbin_816 (coe v0) (coe v3) (coe v4) (coe v5))
                (coe
                   d_pex_806 (coe v0) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe v1))
         _ -> coe v2)
-- Once.Format.Print.pspine
d_pspine_820 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine_820 v0
  = let v1
          = d_pex_806
              (coe (6 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pspine'8242'_822 (coe v2) (coe v3)
                (coe d_isCompose_794 (coe d_headOf_798 (coe v2)))
         _ -> coe v1)
-- Once.Format.Print.pspine′
d_pspine'8242'_822 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine'8242'_822 v0 v1 v2
  = let v3
          = d__'8853''7496'__394
              (coe d_pspine_820 (coe v0))
              (coe
                 d__'8853''7496'__394
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v4)
                 (coe
                    d_pex_806 (coe (6 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                  -> coe d_pcompose_810 (coe (6 :: Integer)) (coe v5) (coe v1)
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.plam
d_plam_824 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam_824 v0 v1
  = coe
      du__'62''62''61''8242'__368
      (coe
         d__'8853''7496'__394 (coe d_txt_404 (coe ("\\" :: Data.Text.Text)))
         (coe
            d__'8853''7496'__394 (coe d_word_438 (coe v0))
            (coe d_plam'8242'_826 (coe v1))))
      (coe
         (\ v2 v3 v4 ->
            coe
              du_pure'8242'_358
              (coe MAlonzo.Code.Once.Format.Doc.C_group_28 (coe v2)) v4))
-- Once.Format.Print.plam′
d_plam'8242'_826 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam'8242'_826 v0
  = let v1
          = d__'8853''7496'__394
              (coe d_txt_404 (coe (" ->" :: Data.Text.Text)))
              (coe
                 du__'62''62''61''8242'__368
                 (coe
                    d__'8853''7496'__394
                    (\ v1 v2 ->
                       coe
                         du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v2)
                    (coe
                       d_pex_806 (coe (0 :: Integer))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0)))
                 (coe
                    (\ v1 v2 v3 ->
                       coe
                         du_pure'8242'_358
                         (coe
                            MAlonzo.Code.Once.Format.Doc.C_nest_26
                            (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v1))
                         v3))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
           -> coe
                d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_word_438 (coe v2))
                   (coe d_plam'8242'_826 (coe v3)))
         _ -> coe v1)
-- Once.Format.Print.plet
d_plet_828 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet_828 v0 v1 v2
  = coe
      du__'62''62''61''8242'__368
      (coe d_plet'8242'_830 (coe v0) (coe v1) (coe v2))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_358
              (coe MAlonzo.Code.Once.Format.Doc.C_group_28 (coe v3)) v5))
-- Once.Format.Print.plet′
d_plet'8242'_830 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet'8242'_830 v0 v1 v2
  = let v3
          = d__'8853''7496'__394
              (coe d_lhead_832 (coe v0) (coe v1))
              (coe
                 d__'8853''7496'__394
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v4)
                 (coe
                    d__'8853''7496'__394
                    (coe d_word_438 (coe ("in" :: Data.Text.Text)))
                    (coe
                       d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                       (coe
                          d_pex_806 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v4 v5 v6
           -> coe
                d__'8853''7496'__394 (coe d_lhead_832 (coe v0) (coe v1))
                (coe
                   d__'8853''7496'__394
                   (\ v7 v8 ->
                      coe
                        du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v8)
                   (coe
                      d__'8853''7496'__394
                      (coe d_word_438 (coe ("in" :: Data.Text.Text)))
                      (coe
                         d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                         (coe d_plet'8242'_830 (coe v4) (coe v5) (coe v6)))))
         _ -> coe v3)
-- Once.Format.Print.lhead
d_lhead_832 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lhead_832 v0 v1
  = coe
      d__'8853''7496'__394
      (coe d_word_438 (coe ("let" :: Data.Text.Text)))
      (coe
         d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
         (coe
            d__'8853''7496'__394 (coe d_word_438 (coe v0))
            (coe
               d__'8853''7496'__394 (coe d_txt_404 (coe (" =" :: Data.Text.Text)))
               (coe
                  du__'62''62''61''8242'__368
                  (coe
                     d__'8853''7496'__394
                     (\ v2 v3 ->
                        coe
                          du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v3)
                     (coe
                        d_pex_806 (coe (0 :: Integer))
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v1)))
                  (coe
                     (\ v2 v3 v4 ->
                        coe
                          du_pure'8242'_358
                          (coe
                             MAlonzo.Code.Once.Format.Doc.C_group_28
                             (coe
                                MAlonzo.Code.Once.Format.Doc.C_nest_26
                                (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v2)))
                          v4))))))
-- Once.Format.Print.pdes
d_pdes_834 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdes_834 v0 v1 v2 v3 v4
  = coe
      du__'62''62''61''8242'__368
      (coe
         d__'8853''7496'__394
         (coe d_word_438 (coe ("destruct" :: Data.Text.Text)))
         (coe
            d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
            (coe
               d__'8853''7496'__394
               (coe
                  d_pex_806 (coe (0 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0))
               (coe
                  d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                  (coe
                     d__'8853''7496'__394
                     (coe d_word_438 (coe ("of" :: Data.Text.Text)))
                     (coe
                        du__'62''62''61''8242'__368
                        (coe
                           d__'8853''7496'__394
                           (\ v5 v6 ->
                              coe
                                du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v6)
                           (coe
                              d__'8853''7496'__394 (coe d_txt_404 (coe ("{ " :: Data.Text.Text)))
                              (coe
                                 d__'8853''7496'__394
                                 (coe d_word_438 (coe ("Left" :: Data.Text.Text)))
                                 (coe
                                    d__'8853''7496'__394
                                    (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                    (coe
                                       d__'8853''7496'__394 (coe d_word_438 (coe v1))
                                       (coe
                                          d__'8853''7496'__394
                                          (coe d_txt_404 (coe (" -> " :: Data.Text.Text)))
                                          (coe
                                             d__'8853''7496'__394
                                             (coe
                                                d_pex_806 (coe (0 :: Integer))
                                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                (coe v2))
                                             (coe
                                                d__'8853''7496'__394
                                                (\ v5 v6 ->
                                                   coe
                                                     du_pure'8242'_358
                                                     (coe MAlonzo.Code.Once.Format.Doc.C_line_16)
                                                     v6)
                                                (coe
                                                   d__'8853''7496'__394
                                                   (coe d_txt_404 (coe ("; " :: Data.Text.Text)))
                                                   (coe
                                                      d__'8853''7496'__394
                                                      (coe
                                                         d_word_438
                                                         (coe ("Right" :: Data.Text.Text)))
                                                      (coe
                                                         d__'8853''7496'__394
                                                         (coe
                                                            d_txt_404 (coe (" " :: Data.Text.Text)))
                                                         (coe
                                                            d__'8853''7496'__394
                                                            (coe d_word_438 (coe v3))
                                                            (coe
                                                               d__'8853''7496'__394
                                                               (coe
                                                                  d_txt_404
                                                                  (coe (" -> " :: Data.Text.Text)))
                                                               (coe
                                                                  d__'8853''7496'__394
                                                                  (coe
                                                                     d_pex_806 (coe (0 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                                     (coe v4))
                                                                  (coe
                                                                     d__'8853''7496'__394
                                                                     (\ v5 v6 ->
                                                                        coe
                                                                          du_pure'8242'_358
                                                                          (coe
                                                                             MAlonzo.Code.Once.Format.Doc.C_line_16)
                                                                          v6)
                                                                     (coe
                                                                        d_txt_404
                                                                        (coe
                                                                           ("}"
                                                                            ::
                                                                            Data.Text.Text))))))))))))))))))
                        (coe
                           (\ v5 v6 v7 ->
                              coe
                                du_pure'8242'_358
                                (coe
                                   MAlonzo.Code.Once.Format.Doc.C_nest_26
                                   (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5))
                                v7))))))))
      (coe
         (\ v5 v6 v7 ->
            coe
              du_pure'8242'_358
              (coe MAlonzo.Code.Once.Format.Doc.C_group_28 (coe v5)) v7))
-- Once.Format.Print.path
d_path_1086 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path_1086 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_word_438 (coe v1)
             (:) v3 v4
               -> coe
                    d__'8853''7496'__394 (coe d_word_438 (coe v1))
                    (coe
                       d__'8853''7496'__394 (coe d_txt_404 (coe ("." :: Data.Text.Text)))
                       (coe d_path_1086 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.spaced
d_spaced_1094 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spaced_1094 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> coe
             d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
             (coe
                d__'8853''7496'__394 (coe d_word_438 (coe v1))
                (coe d_spaced_1094 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pdecl
d_pdecl_1100 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdecl_1100 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v1 v2
        -> coe
             du__'62''62''61''8242'__368
             (coe
                d__'8853''7496'__394 (coe d_name_508 (coe v1))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" :" :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394
                      (\ v3 v4 ->
                         coe
                           du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v4)
                      (coe
                         d_pty_534 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))
             (coe
                (\ v3 v4 v5 ->
                   coe
                     du_pure'8242'_358
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_28
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_26
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v3)))
                     v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v1 v2
        -> let v3 = d_lams_772 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       du__'62''62''61''8242'__368
                       (coe
                          d__'8853''7496'__394 (coe d_name_508 (coe v1))
                          (coe
                             d__'8853''7496'__394 (coe d_spaced_1094 (coe v4))
                             (coe
                                d__'8853''7496'__394 (coe d_txt_404 (coe (" =" :: Data.Text.Text)))
                                (coe
                                   d__'8853''7496'__394
                                   (\ v6 v7 ->
                                      coe
                                        du_pure'8242'_358
                                        (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v7)
                                   (coe
                                      d_pex_806 (coe (0 :: Integer))
                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v5))))))
                       (coe
                          (\ v6 v7 v8 ->
                             coe
                               du_pure'8242'_358
                               (coe
                                  MAlonzo.Code.Once.Format.Doc.C_group_28
                                  (coe
                                     MAlonzo.Code.Once.Format.Doc.C_nest_26
                                     (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v6)))
                               v8))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v1 v2
        -> coe
             du__'62''62''61''8242'__368
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("signature" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394 (coe d_word_438 (coe v1))
                      (coe
                         d__'8853''7496'__394 (coe d_txt_404 (coe (" :" :: Data.Text.Text)))
                         (coe
                            d__'8853''7496'__394
                            (\ v3 v4 ->
                               coe
                                 du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16) v4)
                            (coe
                               d_pty_534 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))))
             (coe
                (\ v3 v4 v5 ->
                   coe
                     du_pure'8242'_358
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_28
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_26
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v3)))
                     v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_118 v1 v2 v3
        -> coe
             du__'62''62''61''8242'__368
             (coe
                d__'8853''7496'__394
                (coe d_word_438 (coe ("type" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                   (coe
                      d__'8853''7496'__394 (coe d_word_438 (coe v1))
                      (coe
                         d__'8853''7496'__394 (coe d_spaced_1094 (coe v2))
                         (coe
                            d__'8853''7496'__394 (coe d_txt_404 (coe (" =" :: Data.Text.Text)))
                            (coe
                               d__'8853''7496'__394
                               (\ v4 v5 ->
                                  coe
                                    du_pure'8242'_358 (coe MAlonzo.Code.Once.Format.Doc.C_line_16)
                                    v5)
                               (coe
                                  d_pty_534 (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))))))))
             (coe
                (\ v4 v5 v6 ->
                   coe
                     du_pure'8242'_358
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_28
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_26
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v4)))
                     v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                      -> coe
                           d__'8853''7496'__394
                           (coe d_word_438 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                              (coe
                                 d__'8853''7496'__394 (coe d_path_1086 (coe v2))
                                 (coe
                                    d__'8853''7496'__394
                                    (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                    (coe
                                       d__'8853''7496'__394
                                       (coe d_word_438 (coe ("as" :: Data.Text.Text)))
                                       (coe
                                          d__'8853''7496'__394
                                          (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                                          (coe d_word_438 (coe v4)))))))
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           d__'8853''7496'__394
                           (coe d_word_438 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__394 (coe d_txt_404 (coe (" " :: Data.Text.Text)))
                              (coe d_path_1086 (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pmodule
d_pmodule_1146 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pmodule_1146 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_128 v1
        -> coe du_go_1154 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.go
d_go_1154 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1154 ~v0 v1 v2 v3 = du_go_1154 v1 v2 v3
du_go_1154 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1154 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_topNotes_442 (coe v2) (coe addInt (coe (1 :: Integer)) (coe v2))
                (coe v1))
             (coe v2)
      (:) v3 v4
        -> let v5 = coe d_pdecl_1100 v3 v1 v2 in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> let v8 = coe du_go_1154 (coe v4) (coe v1) (coe v7) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                                    (coe d_topNotes_442 (coe v2) (coe v7) (coe v1))
                                    (coe
                                       MAlonzo.Code.Once.Format.Doc.C__'60''62'__24 (coe v6)
                                       (coe
                                          MAlonzo.Code.Once.Format.Doc.C__'60''62'__24
                                          (coe MAlonzo.Code.Once.Format.Doc.C_newline_18)
                                          (coe v9))))
                                 (coe v10)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.format
d_format_1204 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_format_1204 v0 v1
  = coe
      MAlonzo.Code.Once.Format.Doc.d_render_292
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_pmodule_1146 v0 (d_trivia_306 (coe v1)) (0 :: Integer)))
