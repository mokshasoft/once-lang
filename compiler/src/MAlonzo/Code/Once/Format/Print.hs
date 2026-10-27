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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Format.Comment
import qualified MAlonzo.Code.Once.Format.Doc
import qualified MAlonzo.Code.Once.Format.Lex
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Lexing
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
  = C_walker_132 Integer T_Line_96 [T_Held_104] Integer
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Format.Print.W.k
d_k_122 :: T_W_110 -> Integer
d_k_122 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.ln
d_ln_124 :: T_W_110 -> T_Line_96
d_ln_124 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.held
d_held_126 :: T_W_110 -> [T_Held_104]
d_held_126 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.breaks
d_breaks_128 :: T_W_110 -> Integer
d_breaks_128 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.acc
d_acc_130 :: T_W_110 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_acc_130 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.promoteR
d_promoteR_134 :: [T_Held_104] -> Bool -> [T_Held_104]
d_promoteR_134 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> case coe v2 of
             C_held'45'comment_106 v4 v5
               -> if coe v1
                    then coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe C_held'45'comment_106 (coe v4) (coe v1))
                           (coe d_promoteR_134 (coe v3) (coe v1))
                    else coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                           (coe d_promoteR_134 (coe v3) (coe v5))
             C_held'45'blank_108
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                    (coe
                       d_promoteR_134 (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.promote
d_promote_148 :: [T_Held_104] -> [T_Held_104]
d_promote_148 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_promoteR_134
         (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Once.Format.Print.settleAt
d_settleAt_152 ::
  Integer ->
  [T_Held_104] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_settleAt_152 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             C_held'45'comment_106 v5 v6
               -> if coe v6
                    then coe
                           d_settleAt_152 (coe v0) (coe v4)
                           (coe
                              d_addTo_50 (coe v0)
                              (coe d_addTop_66 (coe C_note'45'comment_8 (coe v5))) (coe v2))
                    else coe
                           d_settleAt_152 (coe v0) (coe v4)
                           (coe d_addTo_50 (coe v0) (coe d_addInner_76 (coe v5)) (coe v2))
             C_held'45'blank_108
               -> coe
                    d_settleAt_152 (coe v0) (coe v4)
                    (coe
                       d_addTo_50 (coe v0) (coe d_addTop_66 (coe C_note'45'blank_10))
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.settle
d_settle_180 :: T_W_110 -> T_W_110
d_settle_180 v0
  = case coe v0 of
      C_walker_132 v1 v2 v3 v4 v5
        -> coe
             C_walker_132 (coe v1) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
             (coe d_settleAt_152 (coe v1) (coe d_promote_148 (coe v3)) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.blankBefore
d_blankBefore_192 :: Integer -> [T_Held_104] -> [T_Held_104]
d_blankBefore_192 v0 v1
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
d_lineEnd_198 :: Bool -> T_W_110 -> T_W_110
d_lineEnd_198 v0 v1
  = case coe v1 of
      C_walker_132 v2 v3 v4 v5 v6
        -> case coe v3 of
             C_line'45'empty_98
               -> coe
                    C_walker_132 (coe v2) (coe v3) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             C_line'45'code_100
               -> coe
                    C_walker_132 (coe v2) (coe C_line'45'empty_98) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             C_line'45'text_102 v7
               -> coe
                    C_walker_132 (coe v2) (coe C_line'45'empty_98)
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
d_isLineEnd_232 :: MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool
d_isLineEnd_232 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TNewline_74
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Parser.Token.C_TEOF_76
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.pending
d_pending_234 :: T_Line_96 -> [T_Held_104] -> [T_Held_104]
d_pending_234 v0 v1
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
d_stepTok_244 ::
  T_W_110 ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool -> T_W_110
d_stepTok_244 v0 v1 v2
  = if coe v2
      then coe d_lineEnd_198 (coe v2) (coe v0)
      else (case coe v0 of
              C_walker_132 v3 v4 v5 v6 v7
                -> coe
                     du_next_266 (coe v1)
                     (coe
                        d_settle_180
                        (coe
                           C_walker_132 (coe v3) (coe v4)
                           (coe
                              d_pending_234 (coe v4) (coe d_blankBefore_192 (coe v6) (coe v5)))
                           (coe v6) (coe v7)))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print._.next
d_next_266 ::
  Integer ->
  T_Line_96 ->
  [T_Held_104] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> T_W_110 -> T_W_110
d_next_266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_next_266 v5 v6
du_next_266 ::
  MAlonzo.Code.Once.Parser.Token.T_Token_6 -> T_W_110 -> T_W_110
du_next_266 v0 v1
  = case coe v1 of
      C_walker_132 v2 v3 v4 v5 v6
        -> coe
             C_walker_132
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_isAnchor_32 (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2))
             (coe C_line'45'code_100)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe (0 :: Integer)) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.stepComment
d_stepComment_272 ::
  T_W_110 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_W_110
d_stepComment_272 v0 v1
  = case coe v0 of
      C_walker_132 v2 v3 v4 v5 v6
        -> case coe v3 of
             C_line'45'empty_98
               -> coe
                    C_walker_132 (coe v2) (coe C_line'45'text_102 (coe v1))
                    (coe d_blankBefore_192 (coe v5) (coe v4)) (coe (0 :: Integer))
                    (coe v6)
             C_line'45'code_100
               -> coe
                    C_walker_132 (coe v2) (coe v3) (coe v4) (coe v5)
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
                    C_walker_132 (coe v2)
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
d_step_306 ::
  T_W_110 -> MAlonzo.Code.Once.Format.Lex.T_Item_6 -> T_W_110
d_step_306 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Format.Lex.C_tok_8 v2
        -> coe
             d_stepTok_244 (coe v0) (coe v2) (coe d_isLineEnd_232 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_comment_10 v2
        -> coe d_stepComment_272 (coe v0) (coe d_trimEnd_36 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_cont_12
        -> coe
             d_lineEnd_198 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.walkItems
d_walkItems_318 ::
  T_W_110 -> [MAlonzo.Code.Once.Format.Lex.T_Item_6] -> T_W_110
d_walkItems_318 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe d_walkItems_318 (coe d_step_306 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.finish
d_finish_328 :: T_W_110 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_finish_328 v0
  = coe
      d_acc_130
      (coe
         d_settle_180
         (coe
            d_lineEnd_198 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe v0)))
-- Once.Format.Print.trivia
d_trivia_332 ::
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_trivia_332 v0
  = coe
      d_finish_328
      (coe
         d_walkItems_318
         (coe
            C_walker_132 (coe (0 :: Integer)) (coe C_line'45'empty_98)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe v0))
-- Once.Format.Print.lookupNotes
d_lookupNotes_336 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Notes_12
d_lookupNotes_336 v0 v1
  = case coe v1 of
      [] -> coe d_noNotes_28
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v0) (coe v4)) (coe v5)
                    (coe d_lookupNotes_336 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.P
d_P_348 :: () -> ()
d_P_348 = erased
-- Once.Format.Print.pure′
d_pure'8242'_354 ::
  () ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pure'8242'_354 ~v0 v1 ~v2 v3 = du_pure'8242'_354 v1 v3
du_pure'8242'_354 ::
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pure'8242'_354 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Format.Print._>>=′_
d__'62''62''61''8242'__364 ::
  () ->
  () ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61''8242'__364 ~v0 ~v1 v2 v3 v4 v5
  = du__'62''62''61''8242'__364 v2 v3 v4 v5
du__'62''62''61''8242'__364 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62''61''8242'__364 v0 v1 v2 v3
  = coe du_next_378 (coe v1) (coe v2) (coe v0 v2 v3)
-- Once.Format.Print._.next
d_next_378 ::
  () ->
  () ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_next_378 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 = du_next_378 v3 v4 v6
du_next_378 ::
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_next_378 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe v0 v3 v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._⊕ᵈ_
d__'8853''7496'__384 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8853''7496'__384 v0 v1
  = coe
      du__'62''62''61''8242'__364 (coe v0)
      (coe
         (\ v2 ->
            coe
              du__'62''62''61''8242'__364 (coe v1)
              (coe
                 (\ v3 v4 v5 ->
                    coe
                      du_pure'8242'_354
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30 (coe v2) (coe v3))
                      v5))))
-- Once.Format.Print.t
d_t_394 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_t_394 v0 v1 v2
  = coe
      du_pure'8242'_354
      (coe MAlonzo.Code.Once.Format.Doc.C_tk_14 (coe v0)) v2
-- Once.Format.Print.␣
d_'9251'_398 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'9251'_398 v0 v1
  = coe
      du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_sp_16) v1
-- Once.Format.Print.inners
d_inners_400 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_inners_400 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
             (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
             (coe MAlonzo.Code.Once.Format.Comment.d_commentRun_174 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.eols
d_eols_404 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_eols_404 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
             (coe
                MAlonzo.Code.Once.Format.Doc.C_eol_28
                (coe MAlonzo.Code.Once.Format.Comment.d_eolText_198 (coe v1)))
             (coe d_eols_404 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.anchor
d_anchor_410 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anchor_410 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
         (coe
            d_inners_400
            (coe d_inner_22 (coe d_lookupNotes_336 (coe v2) (coe v1))))
         (coe
            MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
            (coe MAlonzo.Code.Once.Format.Doc.C_tk_14 (coe v0))
            (coe
               d_eols_404
               (coe d_after_24 (coe d_lookupNotes_336 (coe v2) (coe v1))))))
      (coe addInt (coe (1 :: Integer)) (coe v2))
-- Once.Format.Print.word
d_word_418 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_word_418 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v0)
         (coe ("compose" :: Data.Text.Text)))
      (coe
         d_t_394
         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 (coe v0)))
      (coe
         d_anchor_410
         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 (coe v0)))
-- Once.Format.Print.tops
d_tops_422 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> Integer -> [T_Note_6]
d_tops_422 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_top_20 (coe d_lookupNotes_336 (coe v1) (coe v0)))
                (coe
                   d_tops_422 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                   (coe v3)))
-- Once.Format.Print.topList
d_topList_434 ::
  Integer ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Note_6]
d_topList_434 v0 v1 v2
  = coe
      d_tops_422 (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
-- Once.Format.Print.runs
d_runs_442 ::
  [T_Note_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Bool -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_runs_442 v0 v1 v2
  = case coe v0 of
      []
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
             (:) v3 v4
               -> coe MAlonzo.Code.Once.Format.Comment.d_commentRun_174 (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v3 of
             C_note'45'comment_8 v5
               -> case coe v1 of
                    []
                      -> coe
                           d_runs_442 (coe v4)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v1))
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (:) v6 v7
                      -> if coe v2
                           then coe
                                  MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                                  (coe MAlonzo.Code.Once.Format.Comment.d_commentRun_174 (coe v1))
                                  (coe
                                     MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                                     (coe MAlonzo.Code.Once.Format.Doc.C_blank_26)
                                     (coe
                                        d_runs_442 (coe v4)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                           else coe
                                  d_runs_442 (coe v4)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                  (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_note'45'blank_10
               -> coe
                    d_runs_442 (coe v4) (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.topDoc
d_topDoc_466 :: [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_topDoc_466 v0
  = coe
      d_runs_442 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Format.Print.hasComment
d_hasComment_470 :: [T_Note_6] -> Bool
d_hasComment_470 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v1 of
             C_note'45'comment_8 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_note'45'blank_10 -> coe d_hasComment_470 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opToken
d_opToken_474 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8
d_opToken_474 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
         (coe
            MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
            (coe '.')))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
               (coe '+')))
         (coe
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
            (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                  (coe '-')))
            (coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                  (coe
                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                     (coe '*')))
               (coe
                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                  (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
               (coe
                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                        (coe '/')))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSlash_56))
                  (coe
                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe
                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                           (coe '%')))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPercent_58))
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                           (coe
                              MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                              (coe '<')))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLt_62))
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                              (coe
                                 MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                 (coe '>')))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGt_66))
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                 (coe
                                    MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                    (coe '|')))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPipe_46))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                    (coe
                                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                       (coe '&')))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAmpersand_60))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                          (coe '@')))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                       (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAt_44))
                                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))))))))
-- Once.Format.Print.isOpChar
d_isOpChar_478 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isOpChar_478 v0
  = let v1
          = coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe
                 eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
                 (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '.'))
              (coe
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
              (coe
                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                    (coe
                       MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                       (coe '+')))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
                 (coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                          (coe '-')))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52))
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                          (coe
                             MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                             (coe '*')))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                (coe '/')))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSlash_56))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                             (coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                (coe
                                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                   (coe '%')))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPercent_58))
                             (coe
                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                   (coe
                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                      (coe '<')))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                   (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLt_62))
                                (coe
                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                      (coe
                                         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                         (coe '>')))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGt_66))
                                   (coe
                                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                         (coe
                                            MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
                                            (coe '|')))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPipe_46))
                                      (coe
                                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                            (coe
                                               MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                               (coe v0) (coe '&')))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAmpersand_60))
                                         (coe
                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                               (coe
                                                  MAlonzo.Code.Data.Char.Properties.d__'8799'__14
                                                  (coe v0) (coe '@')))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAt_44))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))))))))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print.allOp
d_allOp_490 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allOp_490 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_isOpChar_478 (coe v1)
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_isOpChar_478 (coe v1)) (coe d_allOp_490 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opTok1
d_opTok1_498 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_opTok1_498 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe d_t_394 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opToks
d_opToks_502 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_opToks_502 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_opTok1_498 (coe d_opToken_474 (coe v1))
             (:) v3 v4
               -> coe
                    d__'8853''7496'__384
                    (coe d_opTok1_498 (coe d_opToken_474 (coe v1)))
                    (coe
                       d__'8853''7496'__384
                       (\ v5 v6 ->
                          coe
                            du_pure'8242'_354
                            (coe
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
                               (coe MAlonzo.Code.Once.Format.Doc.C_sp_16)
                               (coe MAlonzo.Code.Once.Format.Doc.C_empty_12))
                            v6)
                       (coe d_opToks_502 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.isOperator
d_isOperator_512 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isOperator_512 v0
  = coe
      d_allOp_490
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Print.name
d_name_516 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_name_516 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_isOperator_512 (coe v0))
      (coe
         d__'8853''7496'__384
         (coe
            d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
         (coe
            d__'8853''7496'__384
            (coe
               d_opToks_502
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
            (coe
               d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))))
      (coe d_word_418 (coe v0))
-- Once.Format.Print.paren
d_paren_520 ::
  Bool ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_paren_520 v0 v1
  = if coe v0
      then coe
             d__'8853''7496'__384
             (coe
                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d__'8853''7496'__384 (coe v1)
                (coe
                   d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))
      else coe v1
-- Once.Format.Print.grade
d_grade_526 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_grade_526 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             d__'8853''7496'__384 (coe d_'9251'_398)
             (coe
                d__'8853''7496'__384
                (coe
                   d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret0_34))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             d__'8853''7496'__384 (coe d_'9251'_398)
             (coe
                d__'8853''7496'__384
                (coe
                   d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret1_32))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             d__'8853''7496'__384 (coe d_'9251'_398)
             (coe
                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.infixOp
d_infixOp_528 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infixOp_528 v0
  = coe
      d__'8853''7496'__384 (coe d_'9251'_398)
      (coe
         d__'8853''7496'__384 (coe d_t_394 (coe v0)) (coe d_'9251'_398))
-- Once.Format.Print.pty
d_pty_532 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pty_532 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe d_word_418 (coe ("Unit" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe d_word_418 (coe ("Void" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe d_word_418 (coe ("Int" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe d_word_418 (coe ("Float" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> coe
             d_paren_520 (coe ltInt (coe (2 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe
                   d_pty_532 (coe (2 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_infixOp_528
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
                   (coe
                      d_pty_532 (coe (3 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (2 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> coe
             d_paren_520 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe
                   d_pty_532 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_infixOp_528
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
                   (coe
                      d_pty_532 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (1 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> coe
             d_paren_520 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe
                   d_pty_532 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__384 (coe d_grade_526 (coe v4))
                   (coe
                      d__'8853''7496'__384 (coe d_'9251'_398)
                      (coe
                         d_pty_532 (coe (0 :: Integer))
                         (coe
                            MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                            (coe ltInt (coe (0 :: Integer)) (coe v0)))
                         (coe v5)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> coe
             d_paren_520 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe d_word_418 (coe ("Act" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d__'8853''7496'__384
                      (coe
                         d_pty_532 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__384 (coe d_'9251'_398)
                         (coe
                            d_pty_532 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> coe
             d_paren_520 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe d_word_418 (coe ("Eff" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d__'8853''7496'__384
                      (coe
                         d_pty_532 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__384 (coe d_'9251'_398)
                         (coe
                            d_pty_532 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe
             d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe
                d__'8853''7496'__384
                (coe d_word_418 (coe ("Mu" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe d_pfunArg_534 (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__384
                       (coe d_word_418 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__384 (coe d_'9251'_398)
                          (coe d_pfunArg_534 (coe v3))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__384
                       (coe d_word_418 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__384 (coe d_'9251'_398)
                          (coe
                             d__'8853''7496'__384
                             (coe
                                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
                             (coe
                                d__'8853''7496'__384
                                (coe d_word_418 (coe ("Act" :: Data.Text.Text)))
                                (coe
                                   d__'8853''7496'__384 (coe d_'9251'_398)
                                   (coe
                                      d__'8853''7496'__384
                                      (coe d_pfun_536 (coe (0 :: Integer)) (coe v3))
                                      (coe
                                         d_t_394
                                         (coe
                                            MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v3
        -> coe d_word_418 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pfunArg
d_pfunArg_534 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfunArg_534 v0
  = let v1
          = d__'8853''7496'__384
              (coe
                 d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
              (coe
                 d__'8853''7496'__384 (coe d_pfun_536 (coe (0 :: Integer)) (coe v0))
                 (coe
                    d_t_394
                    (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
           -> coe d_word_418 (coe ("Id" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.pfun
d_pfun_536 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfun_536 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v2
        -> coe
             d_paren_520 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384 (coe d_word_418 (coe ("K" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d_pty_532 (coe (3 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe d_word_418 (coe ("Id" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v2 v3
        -> coe
             d_paren_520 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384 (coe d_pfun_536 (coe (0 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_infixOp_528
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
                   (coe d_pfun_536 (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v2 v3
        -> coe
             d_paren_520 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384 (coe d_pfun_536 (coe (1 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_infixOp_528
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
                   (coe d_pfun_536 (coe (2 :: Integer)) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.toPoly
d_toPoly_640 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_toPoly_640 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
             (coe d_toPoly_640 (coe v1)) (coe d_toPoly_640 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30
             (coe d_toPoly_640 (coe v1)) (coe d_toPoly_640 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
                                  (coe d_toPoly_640 (coe v1)) (coe v4) (coe d_toPoly_640 (coe v3))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34
                                  (coe d_toPoly_640 (coe v1)) (coe d_toPoly_640 (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36
                           (coe d_toPoly_640 (coe v1)) (coe d_toPoly_640 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38
             (coe d_toPolyF_642 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40
             (coe d_toPolyF_642 (coe v1)) (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.toPolyF
d_toPolyF_642 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8
d_toPolyF_642 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12
             (coe d_toPoly_640 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16
             (coe d_toPolyF_642 (coe v1)) (coe d_toPolyF_642 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18
             (coe d_toPolyF_642 (coe v1)) (coe d_toPolyF_642 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gty
d_gty_686 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gty_686 v0 v1 v2
  = coe d_pty_532 (coe v0) (coe v1) (coe d_toPoly_640 (coe v2))
-- Once.Format.Print.opTok
d_opTok_694 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8
d_opTok_694 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSlash_56
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPercent_58
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLt_62
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLe_64
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGt_66
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TGe_68
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEqEq_70
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TNeq_72
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opLevel
d_opLevel_696 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Integer
d_opLevel_696 v0
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
-- Once.Format.Print.lams
d_lams_698 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lams_698 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_lams_698 (coe v3))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_lams_698 (coe v3)))
         _ -> coe v1)
-- Once.Format.Print.startsNeg
d_startsNeg_706 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_startsNeg_706 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.isCompose
d_isCompose_708 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_isCompose_708 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v2
           -> coe
                MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
                (coe ("compose" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.headOf
d_headOf_712 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_headOf_712 v0
  = let v1 = coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3 -> coe v2
         _ -> coe v1)
-- Once.Format.Print.leftLevel
d_leftLevel_720 :: Integer -> Integer
d_leftLevel_720 v0
  = case coe v0 of
      1 -> coe (2 :: Integer)
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) -> coe v0
      _ -> coe v0
-- Once.Format.Print.dotted
d_dotted_724 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dotted_724 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_word_418 (coe v1)
             (:) v3 v4
               -> coe
                    d__'8853''7496'__384 (coe d_word_418 (coe v1))
                    (coe
                       d__'8853''7496'__384
                       (coe d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                       (coe d_dotted_724 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pex
d_pex_732 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pex_732 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
        -> coe d_name_516 (coe v3)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
        -> coe
             d__'8853''7496'__384 (coe d_word_418 (coe v3))
             (coe
                d__'8853''7496'__384
                (coe d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAt_44))
                (coe d_word_418 (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v4
               -> coe d_dotted_724 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
        -> coe
             d_pcomp_734 (coe v0)
             (coe d_isCompose_708 (coe d_headOf_712 (coe v3))) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
        -> coe
             d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plam_750 (coe v3) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
        -> coe
             d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plet_754 (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
        -> coe
             du__'62''62''61''8242'__364
             (coe
                d__'8853''7496'__384
                (coe
                   d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_pex_732 (coe (0 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                   (coe
                      d__'8853''7496'__384
                      (coe
                         d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TComma_40))
                      (coe
                         d__'8853''7496'__384
                         (\ v5 v6 ->
                            coe
                              du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v6)
                         (coe
                            d__'8853''7496'__384
                            (coe
                               d_pex_732 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                            (coe
                               d_t_394
                               (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))))))
             (coe
                (\ v5 v6 v7 ->
                   coe
                     du_pure'8242'_354
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_34
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_32
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5)))
                     v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
        -> coe
             d_paren_520 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_pdes_760 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             d__'8853''7496'__384
             (coe
                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
        -> coe
             d_anchor_410
             (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TInt_12 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
        -> coe
             d_anchor_410
             (coe
                MAlonzo.Code.Once.Spec.Surface.Lexing.C_TFloat_14 (coe v3) (coe v4)
                (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
        -> coe
             d__'8853''7496'__384
             (coe
                d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d__'8853''7496'__384
                (coe
                   d_pex_732 (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_infixOp_528
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                   (coe
                      d__'8853''7496'__384
                      (coe
                         d_gty_686 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                      (coe
                         d_t_394
                         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
        -> coe
             du__'62''62''61''8242'__364
             (coe
                d_paren_520 (coe ltInt (coe d_opLevel_696 (coe v3)) (coe v0))
                (coe
                   d_pbin_742 (coe d_opLevel_696 (coe v3)) (coe v3) (coe v4)
                   (coe v5)))
             (coe
                (\ v6 v7 v8 ->
                   coe
                     du_pure'8242'_354
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_34
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_32
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v6)))
                     v8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
        -> coe
             d_paren_520 (coe ltInt (coe (4 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__384
                (coe
                   d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52))
                (coe
                   d__'8853''7496'__384
                   (\ v4 v5 ->
                      coe
                        du_pure'8242'_354
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe d_startsNeg_706 (coe v3))
                           (coe MAlonzo.Code.Once.Format.Doc.C_sp_16)
                           (coe MAlonzo.Code.Once.Format.Doc.C_empty_12))
                        v5)
                   (coe
                      d_pex_732 (coe (4 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pcomp
d_pcomp_734 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcomp_734 v0 v1 v2 v3
  = let v4
          = coe
              du__'62''62''61''8242'__364
              (coe
                 d_paren_520 (coe ltInt (coe (5 :: Integer)) (coe v0))
                 (coe
                    d__'8853''7496'__384 (coe d_pspine_746 (coe v2))
                    (coe
                       d__'8853''7496'__384
                       (\ v4 v5 ->
                          coe
                            du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v5)
                       (coe
                          d_pex_732 (coe (6 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)))))
              (coe
                 (\ v4 v5 v6 ->
                    coe
                      du_pure'8242'_354
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C_group_34
                         (coe
                            MAlonzo.Code.Once.Format.Doc.C_nest_32
                            (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v4)))
                      v6)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v5 v6
                  -> coe d_pcompose_736 (coe v0) (coe v6) (coe v3)
                _ -> coe v4
         _ -> coe v4)
-- Once.Format.Print.pcompose
d_pcompose_736 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcompose_736 v0 v1 v2
  = coe
      du__'62''62''61''8242'__364
      (coe
         d_paren_520 (coe ltInt (coe (0 :: Integer)) (coe v0))
         (coe
            d__'8853''7496'__384 (coe d_pchainC_738 (coe v1))
            (coe
               d__'8853''7496'__384
               (coe
                  d__'8853''7496'__384
                  (\ v3 v4 ->
                     coe
                       du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                  (coe
                     d__'8853''7496'__384
                     (coe d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                     (coe d_'9251'_398)))
               (coe
                  d_pex_732 (coe (1 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_354
              (coe
                 MAlonzo.Code.Once.Format.Doc.C_group_34
                 (coe
                    MAlonzo.Code.Once.Format.Doc.C_nest_32
                    (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v3)))
              v5))
-- Once.Format.Print.pchainC
d_pchainC_738 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC_738 v0
  = let v1
          = d_pex_732
              (coe (1 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pchainC'8242'_740
                (coe d_isCompose_708 (coe d_headOf_712 (coe v2))) (coe v2) (coe v3)
         _ -> coe v1)
-- Once.Format.Print.pchainC′
d_pchainC'8242'_740 ::
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC'8242'_740 v0 v1 v2
  = let v3
          = d_pcomp_734
              (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v1) (coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
                  -> coe
                       d__'8853''7496'__384 (coe d_pchainC_738 (coe v5))
                       (coe
                          d__'8853''7496'__384
                          (coe
                             d__'8853''7496'__384
                             (\ v6 v7 ->
                                coe
                                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v7)
                             (coe
                                d__'8853''7496'__384
                                (coe d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                                (coe d_'9251'_398)))
                          (coe
                             d_pex_732 (coe (1 :: Integer))
                             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.pbin
d_pbin_742 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pbin_742 v0 v1 v2 v3
  = coe
      d__'8853''7496'__384 (coe d_pleft_744 (coe v0) (coe v2))
      (coe
         d__'8853''7496'__384
         (\ v4 v5 ->
            coe
              du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v5)
         (coe
            d__'8853''7496'__384 (coe d_t_394 (coe d_opTok_694 (coe v1)))
            (coe
               d__'8853''7496'__384 (coe d_'9251'_398)
               (coe
                  d_pex_732 (coe addInt (coe (1 :: Integer)) (coe v0))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)))))
-- Once.Format.Print.pleft
d_pleft_744 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pleft_744 v0 v1
  = let v2
          = d_pex_732
              (coe d_leftLevel_720 (coe v0))
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe eqInt (coe v0) (coe d_opLevel_696 (coe v3)))
                   (coe ltInt (coe (1 :: Integer)) (coe v0)))
                (coe d_pbin_742 (coe v0) (coe v3) (coe v4) (coe v5))
                (coe
                   d_pex_732 (coe d_leftLevel_720 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1))
         _ -> coe v2)
-- Once.Format.Print.pspine
d_pspine_746 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine_746 v0
  = let v1
          = d_pex_732
              (coe (6 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pspine'8242'_748
                (coe d_isCompose_708 (coe d_headOf_712 (coe v2))) (coe v2) (coe v3)
         _ -> coe v1)
-- Once.Format.Print.pspine′
d_pspine'8242'_748 ::
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine'8242'_748 v0 v1 v2
  = let v3
          = d__'8853''7496'__384
              (coe d_pspine_746 (coe v1))
              (coe
                 d__'8853''7496'__384
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                 (coe
                    d_pex_732 (coe (6 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
                  -> coe d_pcompose_736 (coe (6 :: Integer)) (coe v5) (coe v2)
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.plam
d_plam_750 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam_750 v0 v1
  = coe
      du__'62''62''61''8242'__364
      (coe
         d__'8853''7496'__384
         (coe
            d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLambda_38))
         (coe
            d__'8853''7496'__384 (coe d_word_418 (coe v0))
            (coe d_plam'8242'_752 (coe v1))))
      (coe
         (\ v2 v3 v4 ->
            coe
              du_pure'8242'_354
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v2)) v4))
-- Once.Format.Print.plam′
d_plam'8242'_752 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam'8242'_752 v0
  = let v1
          = d__'8853''7496'__384
              (coe d_'9251'_398)
              (coe
                 d__'8853''7496'__384
                 (coe
                    d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                 (coe
                    du__'62''62''61''8242'__364
                    (coe
                       d__'8853''7496'__384
                       (\ v1 v2 ->
                          coe
                            du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v2)
                       (coe
                          d_pex_732 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0)))
                    (coe
                       (\ v1 v2 v3 ->
                          coe
                            du_pure'8242'_354
                            (coe
                               MAlonzo.Code.Once.Format.Doc.C_nest_32
                               (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v1))
                            v3)))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
           -> coe
                d__'8853''7496'__384 (coe d_'9251'_398)
                (coe
                   d__'8853''7496'__384 (coe d_word_418 (coe v2))
                   (coe d_plam'8242'_752 (coe v3)))
         _ -> coe v1)
-- Once.Format.Print.plet
d_plet_754 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet_754 v0 v1 v2
  = coe
      du__'62''62''61''8242'__364
      (coe d_plet'8242'_756 (coe v0) (coe v1) (coe v2))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_354
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v3)) v5))
-- Once.Format.Print.plet′
d_plet'8242'_756 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet'8242'_756 v0 v1 v2
  = let v3
          = d__'8853''7496'__384
              (coe d_lhead_758 (coe v0) (coe v1))
              (coe
                 d__'8853''7496'__384
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                 (coe
                    d__'8853''7496'__384
                    (coe d_word_418 (coe ("in" :: Data.Text.Text)))
                    (coe
                       d__'8853''7496'__384 (coe d_'9251'_398)
                       (coe
                          d_pex_732 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v4 v5 v6
           -> coe
                d__'8853''7496'__384 (coe d_lhead_758 (coe v0) (coe v1))
                (coe
                   d__'8853''7496'__384
                   (\ v7 v8 ->
                      coe
                        du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v8)
                   (coe
                      d__'8853''7496'__384
                      (coe d_word_418 (coe ("in" :: Data.Text.Text)))
                      (coe
                         d__'8853''7496'__384 (coe d_'9251'_398)
                         (coe d_plet'8242'_756 (coe v4) (coe v5) (coe v6)))))
         _ -> coe v3)
-- Once.Format.Print.lhead
d_lhead_758 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lhead_758 v0 v1
  = coe
      d__'8853''7496'__384
      (coe d_word_418 (coe ("let" :: Data.Text.Text)))
      (coe
         d__'8853''7496'__384 (coe d_'9251'_398)
         (coe
            d__'8853''7496'__384 (coe d_word_418 (coe v0))
            (coe
               d__'8853''7496'__384 (coe d_'9251'_398)
               (coe
                  d__'8853''7496'__384
                  (coe
                     d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                  (coe
                     du__'62''62''61''8242'__364
                     (coe
                        d__'8853''7496'__384
                        (\ v2 v3 ->
                           coe
                             du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v3)
                        (coe
                           d_pex_732 (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v1)))
                     (coe
                        (\ v2 v3 v4 ->
                           coe
                             du_pure'8242'_354
                             (coe
                                MAlonzo.Code.Once.Format.Doc.C_group_34
                                (coe
                                   MAlonzo.Code.Once.Format.Doc.C_nest_32
                                   (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v2)))
                             v4)))))))
-- Once.Format.Print.pdes
d_pdes_760 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdes_760 v0 v1 v2 v3 v4
  = coe
      du__'62''62''61''8242'__364
      (coe
         d__'8853''7496'__384
         (coe d_word_418 (coe ("destruct" :: Data.Text.Text)))
         (coe
            d__'8853''7496'__384 (coe d_'9251'_398)
            (coe
               d__'8853''7496'__384
               (coe
                  d_pex_732 (coe (0 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0))
               (coe
                  d__'8853''7496'__384 (coe d_'9251'_398)
                  (coe
                     d__'8853''7496'__384
                     (coe d_word_418 (coe ("of" :: Data.Text.Text)))
                     (coe
                        du__'62''62''61''8242'__364
                        (coe
                           d__'8853''7496'__384
                           (\ v5 v6 ->
                              coe
                                du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v6)
                           (coe
                              d__'8853''7496'__384
                              (coe
                                 d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLBrace_22))
                              (coe
                                 d__'8853''7496'__384 (coe d_'9251'_398)
                                 (coe
                                    d__'8853''7496'__384
                                    (coe d_word_418 (coe ("Left" :: Data.Text.Text)))
                                    (coe
                                       d__'8853''7496'__384 (coe d_'9251'_398)
                                       (coe
                                          d__'8853''7496'__384 (coe d_word_418 (coe v1))
                                          (coe
                                             d__'8853''7496'__384
                                             (coe
                                                d_infixOp_528
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                                             (coe
                                                d__'8853''7496'__384
                                                (coe
                                                   d_pex_732 (coe (0 :: Integer))
                                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                   (coe v2))
                                                (coe
                                                   d__'8853''7496'__384
                                                   (\ v5 v6 ->
                                                      coe
                                                        du_pure'8242'_354
                                                        (coe MAlonzo.Code.Once.Format.Doc.C_line_22)
                                                        v6)
                                                   (coe
                                                      d__'8853''7496'__384
                                                      (coe
                                                         d_t_394
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSemicolon_42))
                                                      (coe
                                                         d__'8853''7496'__384 (coe d_'9251'_398)
                                                         (coe
                                                            d__'8853''7496'__384
                                                            (coe
                                                               d_word_418
                                                               (coe ("Right" :: Data.Text.Text)))
                                                            (coe
                                                               d__'8853''7496'__384
                                                               (coe d_'9251'_398)
                                                               (coe
                                                                  d__'8853''7496'__384
                                                                  (coe d_word_418 (coe v3))
                                                                  (coe
                                                                     d__'8853''7496'__384
                                                                     (coe
                                                                        d_infixOp_528
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                                                                     (coe
                                                                        d__'8853''7496'__384
                                                                        (coe
                                                                           d_pex_732
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                                           (coe v4))
                                                                        (coe
                                                                           d__'8853''7496'__384
                                                                           (\ v5 v6 ->
                                                                              coe
                                                                                du_pure'8242'_354
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Format.Doc.C_line_22)
                                                                                v6)
                                                                           (coe
                                                                              d_t_394
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRBrace_24)))))))))))))))))))
                        (coe
                           (\ v5 v6 v7 ->
                              coe
                                du_pure'8242'_354
                                (coe
                                   MAlonzo.Code.Once.Format.Doc.C_nest_32
                                   (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5))
                                v7))))))))
      (coe
         (\ v5 v6 v7 ->
            coe
              du_pure'8242'_354
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v5)) v7))
-- Once.Format.Print.path
d_path_1012 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path_1012 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_word_418 (coe v1)
             (:) v3 v4
               -> coe
                    d__'8853''7496'__384 (coe d_word_418 (coe v1))
                    (coe
                       d__'8853''7496'__384
                       (coe d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                       (coe d_path_1012 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.spaced
d_spaced_1020 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spaced_1020 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> coe
             d__'8853''7496'__384 (coe d_'9251'_398)
             (coe
                d__'8853''7496'__384 (coe d_word_418 (coe v1))
                (coe d_spaced_1020 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pbody
d_pbody_1026 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pbody_1026 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v1 v2
        -> coe
             d__'8853''7496'__384 (coe d_name_516 (coe v1))
             (coe
                d__'8853''7496'__384 (coe d_'9251'_398)
                (coe
                   d__'8853''7496'__384
                   (coe
                      d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                   (coe
                      d__'8853''7496'__384
                      (\ v3 v4 ->
                         coe
                           du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                      (coe
                         d_pty_532 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v1 v2
        -> coe
             d__'8853''7496'__384 (coe d_name_516 (coe v1))
             (coe
                d__'8853''7496'__384
                (coe
                   d_spaced_1020
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_lams_698 (coe v2))))
                (coe
                   d__'8853''7496'__384 (coe d_'9251'_398)
                   (coe
                      d__'8853''7496'__384
                      (coe
                         d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                      (coe
                         d__'8853''7496'__384
                         (\ v3 v4 ->
                            coe
                              du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                         (coe
                            d_pex_732 (coe (0 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_lams_698 (coe v2))))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v1 v2
        -> coe
             d__'8853''7496'__384
             (coe d_word_418 (coe ("signature" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__384 (coe d_'9251'_398)
                (coe
                   d__'8853''7496'__384 (coe d_word_418 (coe v1))
                   (coe
                      d__'8853''7496'__384 (coe d_'9251'_398)
                      (coe
                         d__'8853''7496'__384
                         (coe
                            d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                         (coe
                            d__'8853''7496'__384
                            (\ v3 v4 ->
                               coe
                                 du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                            (coe
                               d_pty_532 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_118 v1 v2 v3
        -> coe
             d__'8853''7496'__384
             (coe d_word_418 (coe ("type" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__384 (coe d_'9251'_398)
                (coe
                   d__'8853''7496'__384 (coe d_word_418 (coe v1))
                   (coe
                      d__'8853''7496'__384 (coe d_spaced_1020 (coe v2))
                      (coe
                         d__'8853''7496'__384 (coe d_'9251'_398)
                         (coe
                            d__'8853''7496'__384
                            (coe
                               d_t_394 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                            (coe
                               d__'8853''7496'__384
                               (\ v4 v5 ->
                                  coe
                                    du_pure'8242'_354 (coe MAlonzo.Code.Once.Format.Doc.C_line_22)
                                    v5)
                               (coe
                                  d_pty_532 (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                      -> coe
                           d__'8853''7496'__384
                           (coe d_word_418 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__384 (coe d_'9251'_398)
                              (coe
                                 d__'8853''7496'__384 (coe d_path_1012 (coe v2))
                                 (coe
                                    d__'8853''7496'__384 (coe d_'9251'_398)
                                    (coe
                                       d__'8853''7496'__384
                                       (coe d_word_418 (coe ("as" :: Data.Text.Text)))
                                       (coe
                                          d__'8853''7496'__384 (coe d_'9251'_398)
                                          (coe d_word_418 (coe v4)))))))
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           d__'8853''7496'__384
                           (coe d_word_418 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__384 (coe d_'9251'_398) (coe d_path_1012 (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pdecl
d_pdecl_1052 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdecl_1052 v0
  = coe
      du__'62''62''61''8242'__364 (coe d_pbody_1026 (coe v0))
      (coe
         (\ v1 v2 v3 ->
            coe
              du_pure'8242'_354
              (coe
                 MAlonzo.Code.Once.Format.Doc.C_group_34
                 (coe
                    MAlonzo.Code.Once.Format.Doc.C_nest_32
                    (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v1)))
              v3))
-- Once.Format.Print.together
d_together_1058 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 -> Bool
d_together_1058 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v5 v6
                  -> coe
                       MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v3)
                       (coe v5)
                _ -> coe v2
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Print.hoist
d_hoist_1064 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_hoist_1064 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v0) (coe v4))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe du_up_1080 (coe v5)))
                       (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe d_hoist_1064 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.up
d_up_1080 ::
  Integer ->
  Integer ->
  T_Notes_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Notes_12 -> T_Notes_12
d_up_1080 ~v0 ~v1 ~v2 ~v3 v4 = du_up_1080 v4
du_up_1080 :: T_Notes_12 -> T_Notes_12
du_up_1080 v0
  = case coe v0 of
      C_notes_26 v1 v2 v3
        -> coe
             C_notes_26
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22 (coe C_note'45'comment_8)
                   (coe v2)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gap
d_gap_1088 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_gap_1088 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_together_1058 (coe v2) (coe v1))
             (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
             (coe MAlonzo.Code.Once.Format.Doc.C_blank_26)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gapEnd
d_gapEnd_1096 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_gapEnd_1096 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Once.Format.Doc.C_blank_26
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.lead
d_lead_1098 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_lead_1098 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe d_topDoc_466 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_hasComment_470 (coe v1))
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                (coe d_topDoc_466 (coe v1))
                (coe MAlonzo.Code.Once.Format.Doc.C_blank_26))
             (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.ending
d_ending_1104 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_ending_1104 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_hasComment_470 (coe v1))
      (coe
         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
         (coe d_gapEnd_1096 (coe v0)) (coe d_topDoc_466 (coe v1)))
      (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
-- Once.Format.Print.pdecls
d_pdecls_1110 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdecls_1110 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_ending_1104 (coe v0)
                (coe
                   d_topList_434 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v3))
                   (coe d_hoist_1064 (coe v3) (coe v2))))
             (coe v3)
      (:) v4 v5
        -> coe
             du_at_1132 (coe v0) (coe v4) (coe v5) (coe v3)
             (coe d_hoist_1064 (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.at
d_at_1132 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_1132 v0 v1 v2 ~v3 v4 v5 = du_at_1132 v0 v1 v2 v4 v5
du_at_1132 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_1132 v0 v1 v2 v3 v4
  = coe
      du_decl_1140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe d_pdecl_1052 v1 v4 v3)
-- Once.Format.Print._._.decl
d_decl_1140 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decl_1140 v0 v1 v2 ~v3 v4 v5 v6 = du_decl_1140 v0 v1 v2 v4 v5 v6
du_decl_1140 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decl_1140 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             du_rest_1150 (coe v0) (coe v1) (coe v3) (coe v4) (coe v6) (coe v7)
             (coe
                d_pdecls_1110
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)) (coe v2)
                (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._._._.rest
d_rest_1150 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rest_1150 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_rest_1150 v0 v1 v4 v5 v6 v7 v8
du_rest_1150 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rest_1150 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                (coe d_gap_1088 (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                   (coe
                      d_lead_1098 (coe v0)
                      (coe d_topList_434 (coe v2) (coe v5) (coe v3)))
                   (coe
                      MAlonzo.Code.Once.Format.Doc.C__'60''62'__30 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                         (coe MAlonzo.Code.Once.Format.Doc.C_newline_24) (coe v7)))))
             (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pmodule
d_pmodule_1156 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pmodule_1156 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_128 v1
        -> coe
             d_pdecls_1110 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.format
d_format_1160 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_format_1160 v0 v1
  = coe
      MAlonzo.Code.Once.Format.Doc.d_render_466
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_pmodule_1156 v0 (d_trivia_332 (coe v1)) (0 :: Integer)))
