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
-- Once.Format.Print.dropLead
d_dropLead_36 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_dropLead_36 v0
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
             (coe d_dropLead_36 (coe v2)) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.trimEnd
d_trimEnd_42 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_trimEnd_42 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_reverse_444
         (d_dropLead_36
            (coe
               MAlonzo.Code.Data.List.Base.du_reverse_444
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))))
-- Once.Format.Print.addTo
d_addTo_46 ::
  Integer ->
  (T_Notes_12 -> T_Notes_12) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_addTo_46 v0 v1 v2
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
                       (coe d_addTo_46 (coe v0) (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.addTop
d_addTop_62 :: T_Note_6 -> T_Notes_12 -> T_Notes_12
d_addTop_62 v0 v1
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
d_addInner_72 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Notes_12 -> T_Notes_12
d_addInner_72 v0 v1
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
d_addAfter_82 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Notes_12 -> T_Notes_12
d_addAfter_82 v0 v1
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
-- Once.Format.Print.lookupNotes
d_lookupNotes_92 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Notes_12
d_lookupNotes_92 v0 v1
  = case coe v1 of
      [] -> coe d_noNotes_28
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe eqInt (coe v0) (coe v4)) (coe v5)
                    (coe d_lookupNotes_92 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.hoist
d_hoist_104 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_hoist_104 v0 v1
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
                          (coe du_up_120 (coe v5)))
                       (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe d_hoist_104 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.up
d_up_120 ::
  Integer ->
  Integer ->
  T_Notes_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Notes_12 -> T_Notes_12
d_up_120 ~v0 ~v1 ~v2 ~v3 v4 = du_up_120 v4
du_up_120 :: T_Notes_12 -> T_Notes_12
du_up_120 v0
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
-- Once.Format.Print.Line
d_Line_128 = ()
data T_Line_128
  = C_line'45'empty_130 | C_line'45'code_132 |
    C_line'45'text_134 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Format.Print.Held
d_Held_136 = ()
data T_Held_136
  = C_held'45'comment_138 MAlonzo.Code.Agda.Builtin.String.T_String_6
                          Bool |
    C_held'45'blank_140
-- Once.Format.Print.W
d_W_142 = ()
data T_W_142
  = C_walker_168 Integer Bool T_Line_128 [T_Held_136] Integer
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Format.Print.W.k
d_k_156 :: T_W_142 -> Integer
d_k_156 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.onLine
d_onLine_158 :: T_W_142 -> Bool
d_onLine_158 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.ln
d_ln_160 :: T_W_142 -> T_Line_128
d_ln_160 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.held
d_held_162 :: T_W_142 -> [T_Held_136]
d_held_162 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.breaks
d_breaks_164 :: T_W_142 -> Integer
d_breaks_164 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.W.acc
d_acc_166 :: T_W_142 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_acc_166 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.promoteR
d_promoteR_170 :: [T_Held_136] -> Bool -> [T_Held_136]
d_promoteR_170 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> case coe v2 of
             C_held'45'comment_138 v4 v5
               -> if coe v1
                    then coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe C_held'45'comment_138 (coe v4) (coe v1))
                           (coe d_promoteR_170 (coe v3) (coe v1))
                    else coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                           (coe d_promoteR_170 (coe v3) (coe v5))
             C_held'45'blank_140
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                    (coe
                       d_promoteR_170 (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.promote
d_promote_184 :: [T_Held_136] -> [T_Held_136]
d_promote_184 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_promoteR_170
         (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Once.Format.Print.settleAt
d_settleAt_188 ::
  Integer ->
  [T_Held_136] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_settleAt_188 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             C_held'45'comment_138 v5 v6
               -> if coe v6
                    then coe
                           d_settleAt_188 (coe v0) (coe v4)
                           (coe
                              d_addTo_46 (coe v0)
                              (coe d_addTop_62 (coe C_note'45'comment_8 (coe v5))) (coe v2))
                    else coe
                           d_settleAt_188 (coe v0) (coe v4)
                           (coe d_addTo_46 (coe v0) (coe d_addInner_72 (coe v5)) (coe v2))
             C_held'45'blank_140
               -> coe
                    d_settleAt_188 (coe v0) (coe v4)
                    (coe
                       d_addTo_46 (coe v0) (coe d_addTop_62 (coe C_note'45'blank_10))
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.settle
d_settle_216 :: T_W_142 -> T_W_142
d_settle_216 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6
        -> coe
             C_walker_168 (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v5)
             (coe d_settleAt_188 (coe v1) (coe d_promote_184 (coe v4)) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.blankBefore
d_blankBefore_230 :: Integer -> [T_Held_136] -> [T_Held_136]
d_blankBefore_230 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         ltInt (coe (2 :: Integer))
         (coe addInt (coe (1 :: Integer)) (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe C_held'45'blank_140)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe v1)
-- Once.Format.Print.lineEnd
d_lineEnd_236 :: Bool -> T_W_142 -> T_W_142
d_lineEnd_236 v0 v1
  = case coe v1 of
      C_walker_168 v2 v3 v4 v5 v6 v7
        -> case coe v4 of
             C_line'45'empty_130
               -> coe
                    C_walker_168 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4) (coe v5)
                    (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7)
             C_line'45'code_132
               -> coe
                    C_walker_168 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe C_line'45'empty_130) (coe v5)
                    (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7)
             C_line'45'text_134 v8
               -> coe
                    C_walker_168 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe C_line'45'empty_130)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe (\ v9 -> coe C_held'45'comment_138 (coe v9) (coe v0)))
                          (coe v8)))
                    (coe (1 :: Integer)) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.isLineEnd
d_isLineEnd_272 :: MAlonzo.Code.Once.Parser.Token.T_Token_6 -> Bool
d_isLineEnd_272 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Token.C_TNewline_74
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Parser.Token.C_TEOF_76
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.pending
d_pending_274 :: T_Line_128 -> [T_Held_136] -> [T_Held_136]
d_pending_274 v0 v1
  = case coe v0 of
      C_line'45'empty_130 -> coe v1
      C_line'45'code_132 -> coe v1
      C_line'45'text_134 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v3 ->
                      coe
                        C_held'45'comment_138 (coe v3)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.hoistAt
d_hoistAt_286 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_hoistAt_286 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.List.Base.du_null_262
         (coe d_inner_22 (coe d_lookupNotes_92 (coe v0) (coe v1))))
      (coe v1) (coe d_hoist_104 (coe v0) (coe v1))
-- Once.Format.Print.hoistW
d_hoistW_292 :: T_W_142 -> T_W_142
d_hoistW_292 v0
  = case coe v0 of
      C_walker_168 v1 v2 v3 v4 v5 v6
        -> coe
             C_walker_168 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe d_hoistAt_286 (coe v1) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.stepTok
d_stepTok_306 :: T_W_142 -> Bool -> Bool -> T_W_142
d_stepTok_306 v0 v1 v2
  = if coe v2
      then coe d_hoistW_292 (coe d_lineEnd_236 (coe v2) (coe v0))
      else (case coe v0 of
              C_walker_168 v3 v4 v5 v6 v7 v8
                -> coe
                     du_next_330 (coe v1)
                     (coe
                        d_settle_216
                        (coe
                           C_walker_168 (coe v3) (coe v4) (coe v5)
                           (coe
                              d_pending_274 (coe v5) (coe d_blankBefore_230 (coe v7) (coe v6)))
                           (coe v7) (coe v8)))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Print._.next
d_next_330 ::
  Integer ->
  Bool ->
  T_Line_128 ->
  [T_Held_136] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool -> T_W_142 -> T_W_142
d_next_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_next_330 v6 v7
du_next_330 :: Bool -> T_W_142 -> T_W_142
du_next_330 v0 v1
  = case coe v1 of
      C_walker_168 v2 v3 v4 v5 v6 v7
        -> coe
             C_walker_168
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
                (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2))
             (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v3) (coe v0))
             (coe C_line'45'code_132)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe (0 :: Integer)) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.afterCode
d_afterCode_338 ::
  Bool ->
  Integer ->
  [T_Held_136] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_W_142
d_afterCode_338 v0 v1 v2 v3 v4 v5
  = if coe v0
      then coe
             C_walker_168 (coe v1) (coe v0) (coe C_line'45'code_132) (coe v2)
             (coe v3)
             (coe
                d_addTo_46
                (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (1 :: Integer))
                (coe d_addAfter_82 (coe v5)) (coe v4))
      else coe
             C_walker_168 (coe v1) (coe v0) (coe C_line'45'code_132)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_held'45'comment_138 (coe v5) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe v3) (coe v4)
-- Once.Format.Print.stepComment
d_stepComment_360 ::
  T_W_142 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_W_142
d_stepComment_360 v0 v1
  = case coe v0 of
      C_walker_168 v2 v3 v4 v5 v6 v7
        -> case coe v4 of
             C_line'45'empty_130
               -> coe
                    C_walker_168 (coe v2) (coe v3)
                    (coe
                       C_line'45'text_134
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                    (coe d_blankBefore_230 (coe v6) (coe v5)) (coe (0 :: Integer))
                    (coe v7)
             C_line'45'code_132
               -> coe
                    d_afterCode_338 (coe v3) (coe v2) (coe v5) (coe v6) (coe v7)
                    (coe v1)
             C_line'45'text_134 v8
               -> coe
                    C_walker_168 (coe v2) (coe v3)
                    (coe
                       C_line'45'text_134
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe v5) (coe v6) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.step
d_step_400 ::
  T_W_142 -> MAlonzo.Code.Once.Format.Lex.T_Item_6 -> T_W_142
d_step_400 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Format.Lex.C_tok_8 v2
        -> coe
             d_stepTok_306 (coe v0) (coe d_isAnchor_32 (coe v2))
             (coe d_isLineEnd_272 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_comment_10 v2
        -> coe d_stepComment_360 (coe v0) (coe d_trimEnd_42 (coe v2))
      MAlonzo.Code.Once.Format.Lex.C_cont_12
        -> coe
             d_lineEnd_236 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.walkItems
d_walkItems_412 ::
  T_W_142 -> [MAlonzo.Code.Once.Format.Lex.T_Item_6] -> T_W_142
d_walkItems_412 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe d_walkItems_412 (coe d_step_400 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.finish
d_finish_422 :: T_W_142 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_finish_422 v0
  = coe
      d_acc_166
      (coe
         d_settle_216
         (coe
            d_lineEnd_236 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
            (coe v0)))
-- Once.Format.Print.trivia
d_trivia_426 ::
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_trivia_426 v0
  = coe
      d_finish_422
      (coe
         d_walkItems_412
         (coe
            C_walker_168 (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
            (coe C_line'45'empty_130)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe v0))
-- Once.Format.Print.P
d_P_430 :: () -> ()
d_P_430 = erased
-- Once.Format.Print.pure′
d_pure'8242'_436 ::
  () ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pure'8242'_436 ~v0 v1 ~v2 v3 = du_pure'8242'_436 v1 v3
du_pure'8242'_436 ::
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pure'8242'_436 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Format.Print._>>=′_
d__'62''62''61''8242'__446 ::
  () ->
  () ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61''8242'__446 ~v0 ~v1 v2 v3 v4 v5
  = du__'62''62''61''8242'__446 v2 v3 v4 v5
du__'62''62''61''8242'__446 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'62''62''61''8242'__446 v0 v1 v2 v3
  = coe du_next_460 (coe v1) (coe v2) (coe v0 v2 v3)
-- Once.Format.Print._.next
d_next_460 ::
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
d_next_460 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 = du_next_460 v3 v4 v6
du_next_460 ::
  (AgdaAny ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_next_460 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe v0 v3 v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._⊕ᵈ_
d__'8853''7496'__466 ::
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8853''7496'__466 v0 v1
  = coe
      du__'62''62''61''8242'__446 (coe v0)
      (coe
         (\ v2 ->
            coe
              du__'62''62''61''8242'__446 (coe v1)
              (coe
                 (\ v3 v4 v5 ->
                    coe
                      du_pure'8242'_436
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30 (coe v2) (coe v3))
                      v5))))
-- Once.Format.Print.t
d_t_476 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_t_476 v0 v1 v2
  = coe
      du_pure'8242'_436
      (coe MAlonzo.Code.Once.Format.Doc.C_tk_14 (coe v0)) v2
-- Once.Format.Print.␣
d_'9251'_480 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'9251'_480 v0 v1
  = coe
      du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_sp_16) v1
-- Once.Format.Print.inners
d_inners_482 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_inners_482 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
             (coe MAlonzo.Code.Once.Format.Doc.C_newline_24)
             (coe MAlonzo.Code.Once.Format.Comment.d_commentRun_174 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.eols
d_eols_486 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_eols_486 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
             (coe
                MAlonzo.Code.Once.Format.Doc.C_eol_28
                (coe MAlonzo.Code.Once.Format.Comment.d_eolText_200 (coe v1)))
             (coe d_eols_486 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.anchor
d_anchor_492 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anchor_492 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
         (coe
            d_inners_482
            (coe d_inner_22 (coe d_lookupNotes_92 (coe v2) (coe v1))))
         (coe
            MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
            (coe MAlonzo.Code.Once.Format.Doc.C_tk_14 (coe v0))
            (coe
               d_eols_486
               (coe d_after_24 (coe d_lookupNotes_92 (coe v2) (coe v1))))))
      (coe addInt (coe (1 :: Integer)) (coe v2))
-- Once.Format.Print.word
d_word_500 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_word_500 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v0)
         (coe ("compose" :: Data.Text.Text)))
      (coe
         d_t_476
         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 (coe v0)))
      (coe
         d_anchor_492
         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 (coe v0)))
-- Once.Format.Print.tops
d_tops_504 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> Integer -> [T_Note_6]
d_tops_504 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_top_20 (coe d_lookupNotes_92 (coe v1) (coe v0)))
                (coe
                   d_tops_504 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                   (coe v3)))
-- Once.Format.Print.topList
d_topList_516 ::
  Integer ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Note_6]
d_topList_516 v0 v1 v2
  = coe
      d_tops_504 (coe v2) (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
-- Once.Format.Print.runs
d_runs_524 ::
  [T_Note_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Bool -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_runs_524 v0 v1 v2
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
                           d_runs_524 (coe v4)
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
                                        d_runs_524 (coe v4)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                           else coe
                                  d_runs_524 (coe v4)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                  (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_note'45'blank_10
               -> coe
                    d_runs_524 (coe v4) (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.topDoc
d_topDoc_548 :: [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_topDoc_548 v0
  = coe
      d_runs_524 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Format.Print.hasComment
d_hasComment_552 :: [T_Note_6] -> Bool
d_hasComment_552 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v1 of
             C_note'45'comment_8 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_note'45'blank_10 -> coe d_hasComment_552 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opToken
d_opToken_556 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8
d_opToken_556 v0
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
d_isOpChar_560 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d_isOpChar_560 v0
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
d_allOp_572 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allOp_572 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_isOpChar_560 (coe v1)
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_isOpChar_560 (coe v1)) (coe d_allOp_572 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opTok1
d_opTok1_580 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_opTok1_580 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe d_t_476 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.opToks
d_opToks_584 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_opToks_584 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_opTok1_580 (coe d_opToken_556 (coe v1))
             (:) v3 v4
               -> coe
                    d__'8853''7496'__466
                    (coe d_opTok1_580 (coe d_opToken_556 (coe v1)))
                    (coe
                       d__'8853''7496'__466
                       (\ v5 v6 ->
                          coe
                            du_pure'8242'_436
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
                       (coe d_opToks_584 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.isOperator
d_isOperator_594 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isOperator_594 v0
  = coe
      d_allOp_572
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Format.Print.name
d_name_598 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_name_598 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_isOperator_594 (coe v0))
      (coe
         d__'8853''7496'__466
         (coe
            d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
         (coe
            d__'8853''7496'__466
            (coe
               d_opToks_584
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
            (coe
               d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))))
      (coe d_word_500 (coe v0))
-- Once.Format.Print.paren
d_paren_602 ::
  Bool ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_paren_602 v0 v1
  = if coe v0
      then coe
             d__'8853''7496'__466
             (coe
                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d__'8853''7496'__466 (coe v1)
                (coe
                   d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))
      else coe v1
-- Once.Format.Print.grade
d_grade_608 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_grade_608 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             d__'8853''7496'__466 (coe d_'9251'_480)
             (coe
                d__'8853''7496'__466
                (coe
                   d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret0_34))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))))
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe
             d__'8853''7496'__466 (coe d_'9251'_480)
             (coe
                d__'8853''7496'__466
                (coe
                   d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TCaret1_32))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))))
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             d__'8853''7496'__466 (coe d_'9251'_480)
             (coe
                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.infixOp
d_infixOp_610 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infixOp_610 v0
  = coe
      d__'8853''7496'__466 (coe d_'9251'_480)
      (coe
         d__'8853''7496'__466 (coe d_t_476 (coe v0)) (coe d_'9251'_480))
-- Once.Format.Print.pty
d_pty_614 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pty_614 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe d_word_500 (coe ("Unit" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe d_word_500 (coe ("Void" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe d_word_500 (coe ("Int" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe d_word_500 (coe ("Float" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> coe
             d_paren_602 (coe ltInt (coe (2 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe
                   d_pty_614 (coe (2 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_infixOp_610
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
                   (coe
                      d_pty_614 (coe (3 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (2 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> coe
             d_paren_602 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe
                   d_pty_614 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_infixOp_610
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
                   (coe
                      d_pty_614 (coe (2 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                         (coe ltInt (coe (1 :: Integer)) (coe v0)))
                      (coe v4))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> coe
             d_paren_602 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe
                   d_pty_614 (coe (1 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__466 (coe d_grade_608 (coe v4))
                   (coe
                      d__'8853''7496'__466 (coe d_'9251'_480)
                      (coe
                         d_pty_614 (coe (0 :: Integer))
                         (coe
                            MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v1)
                            (coe ltInt (coe (0 :: Integer)) (coe v0)))
                         (coe v5)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> coe
             d_paren_602 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe d_word_500 (coe ("Act" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d__'8853''7496'__466
                      (coe
                         d_pty_614 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__466 (coe d_'9251'_480)
                         (coe
                            d_pty_614 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> coe
             d_paren_602 (coe ltInt (coe (3 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe d_word_500 (coe ("Eff" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d__'8853''7496'__466
                      (coe
                         d_pty_614 (coe (3 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
                      (coe
                         d__'8853''7496'__466 (coe d_'9251'_480)
                         (coe
                            d_pty_614 (coe (3 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe
             d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe
                d__'8853''7496'__466
                (coe d_word_500 (coe ("Mu" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe d_pfunArg_616 (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__466
                       (coe d_word_500 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__466 (coe d_'9251'_480)
                          (coe d_pfunArg_616 (coe v3))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
                    (coe
                       d__'8853''7496'__466
                       (coe d_word_500 (coe ("Nu" :: Data.Text.Text)))
                       (coe
                          d__'8853''7496'__466 (coe d_'9251'_480)
                          (coe
                             d__'8853''7496'__466
                             (coe
                                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
                             (coe
                                d__'8853''7496'__466
                                (coe d_word_500 (coe ("Act" :: Data.Text.Text)))
                                (coe
                                   d__'8853''7496'__466 (coe d_'9251'_480)
                                   (coe
                                      d__'8853''7496'__466
                                      (coe d_pfun_618 (coe (0 :: Integer)) (coe v3))
                                      (coe
                                         d_t_476
                                         (coe
                                            MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v3
        -> coe d_word_500 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pfunArg
d_pfunArg_616 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfunArg_616 v0
  = let v1
          = d__'8853''7496'__466
              (coe
                 d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
              (coe
                 d__'8853''7496'__466 (coe d_pfun_618 (coe (0 :: Integer)) (coe v0))
                 (coe
                    d_t_476
                    (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
           -> coe d_word_500 (coe ("Id" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.pfun
d_pfun_618 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pfun_618 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v2
        -> coe
             d_paren_602 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466 (coe d_word_500 (coe ("K" :: Data.Text.Text)))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d_pty_614 (coe (3 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe d_word_500 (coe ("Id" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v2 v3
        -> coe
             d_paren_602 (coe ltInt (coe (0 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466 (coe d_pfun_618 (coe (0 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_infixOp_610
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TPlus_50))
                   (coe d_pfun_618 (coe (1 :: Integer)) (coe v3))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v2 v3
        -> coe
             d_paren_602 (coe ltInt (coe (1 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466 (coe d_pfun_618 (coe (1 :: Integer)) (coe v2))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_infixOp_610
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TStar_54))
                   (coe d_pfun_618 (coe (2 :: Integer)) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.toPoly
d_toPoly_722 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_toPoly_722 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
             (coe d_toPoly_722 (coe v1)) (coe d_toPoly_722 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30
             (coe d_toPoly_722 (coe v1)) (coe d_toPoly_722 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
                                  (coe d_toPoly_722 (coe v1)) (coe v4) (coe d_toPoly_722 (coe v3))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34
                                  (coe d_toPoly_722 (coe v1)) (coe d_toPoly_722 (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36
                           (coe d_toPoly_722 (coe v1)) (coe d_toPoly_722 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38
             (coe d_toPolyF_724 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40
             (coe d_toPolyF_724 (coe v1)) (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.toPolyF
d_toPolyF_724 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8
d_toPolyF_724 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12
             (coe d_toPoly_722 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16
             (coe d_toPolyF_724 (coe v1)) (coe d_toPolyF_724 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18
             (coe d_toPolyF_724 (coe v1)) (coe d_toPolyF_724 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gty
d_gty_768 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gty_768 v0 v1 v2
  = coe d_pty_614 (coe v0) (coe v1) (coe d_toPoly_722 (coe v2))
-- Once.Format.Print.opTok
d_opTok_776 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8
d_opTok_776 v0
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
d_opLevel_778 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Integer
d_opLevel_778 v0
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
d_lams_780 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lams_780 v0
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
                      (coe d_lams_780 (coe v3))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_lams_780 (coe v3)))
         _ -> coe v1)
-- Once.Format.Print.startsNeg
d_startsNeg_788 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_startsNeg_788 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Print.isCompose
d_isCompose_790 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> Bool
d_isCompose_790 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v2
           -> coe
                MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
                (coe ("compose" :: Data.Text.Text))
         _ -> coe v1)
-- Once.Format.Print.headOf
d_headOf_794 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_headOf_794 v0
  = let v1 = coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3 -> coe v2
         _ -> coe v1)
-- Once.Format.Print.leftLevel
d_leftLevel_802 :: Integer -> Integer
d_leftLevel_802 v0
  = case coe v0 of
      1 -> coe (2 :: Integer)
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) -> coe v0
      _ -> coe v0
-- Once.Format.Print.dotted
d_dotted_806 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dotted_806 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_word_500 (coe v1)
             (:) v3 v4
               -> coe
                    d__'8853''7496'__466 (coe d_word_500 (coe v1))
                    (coe
                       d__'8853''7496'__466
                       (coe d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                       (coe d_dotted_806 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pex
d_pex_814 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pex_814 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
        -> coe d_name_598 (coe v3)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
        -> coe
             d__'8853''7496'__466 (coe d_word_500 (coe v3))
             (coe
                d__'8853''7496'__466
                (coe d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TAt_44))
                (coe d_word_500 (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v4
               -> coe d_dotted_806 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
        -> coe
             d_pcomp_816 (coe v0)
             (coe d_isCompose_790 (coe d_headOf_794 (coe v3))) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
        -> coe
             d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plam_832 (coe v3) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
        -> coe
             d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_plet_836 (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
        -> coe
             du__'62''62''61''8242'__446
             (coe
                d__'8853''7496'__466
                (coe
                   d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_pex_814 (coe (0 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                   (coe
                      d__'8853''7496'__466
                      (coe
                         d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TComma_40))
                      (coe
                         d__'8853''7496'__466
                         (\ v5 v6 ->
                            coe
                              du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v6)
                         (coe
                            d__'8853''7496'__466
                            (coe
                               d_pex_814 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                            (coe
                               d_t_476
                               (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))))))
             (coe
                (\ v5 v6 v7 ->
                   coe
                     du_pure'8242'_436
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_34
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_32
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5)))
                     v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
        -> coe
             d_paren_602 (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1))
             (coe d_pdes_842 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             d__'8853''7496'__466
             (coe
                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
        -> coe
             d_anchor_492
             (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TInt_12 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
        -> coe
             d_anchor_492
             (coe
                MAlonzo.Code.Once.Spec.Surface.Lexing.C_TFloat_14 (coe v3) (coe v4)
                (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
        -> coe
             d__'8853''7496'__466
             (coe
                d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLParen_18))
             (coe
                d__'8853''7496'__466
                (coe
                   d_pex_814 (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_infixOp_610
                      (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                   (coe
                      d__'8853''7496'__466
                      (coe
                         d_gty_768 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v4))
                      (coe
                         d_t_476
                         (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRParen_20)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
        -> coe
             du__'62''62''61''8242'__446
             (coe
                d_paren_602 (coe ltInt (coe d_opLevel_778 (coe v3)) (coe v0))
                (coe
                   d_pbin_824 (coe d_opLevel_778 (coe v3)) (coe v3) (coe v4)
                   (coe v5)))
             (coe
                (\ v6 v7 v8 ->
                   coe
                     du_pure'8242'_436
                     (coe
                        MAlonzo.Code.Once.Format.Doc.C_group_34
                        (coe
                           MAlonzo.Code.Once.Format.Doc.C_nest_32
                           (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v6)))
                     v8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
        -> coe
             d_paren_602 (coe ltInt (coe (4 :: Integer)) (coe v0))
             (coe
                d__'8853''7496'__466
                (coe
                   d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TMinus_52))
                (coe
                   d__'8853''7496'__466
                   (\ v4 v5 ->
                      coe
                        du_pure'8242'_436
                        (coe
                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                           (coe d_startsNeg_788 (coe v3))
                           (coe MAlonzo.Code.Once.Format.Doc.C_sp_16)
                           (coe MAlonzo.Code.Once.Format.Doc.C_empty_12))
                        v5)
                   (coe
                      d_pex_814 (coe (4 :: Integer))
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pcomp
d_pcomp_816 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcomp_816 v0 v1 v2 v3
  = let v4
          = coe
              du__'62''62''61''8242'__446
              (coe
                 d_paren_602 (coe ltInt (coe (5 :: Integer)) (coe v0))
                 (coe
                    d__'8853''7496'__466 (coe d_pspine_828 (coe v2))
                    (coe
                       d__'8853''7496'__466
                       (\ v4 v5 ->
                          coe
                            du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v5)
                       (coe
                          d_pex_814 (coe (6 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)))))
              (coe
                 (\ v4 v5 v6 ->
                    coe
                      du_pure'8242'_436
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
                  -> coe d_pcompose_818 (coe v0) (coe v6) (coe v3)
                _ -> coe v4
         _ -> coe v4)
-- Once.Format.Print.pcompose
d_pcompose_818 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pcompose_818 v0 v1 v2
  = coe
      du__'62''62''61''8242'__446
      (coe
         d_paren_602 (coe ltInt (coe (0 :: Integer)) (coe v0))
         (coe
            d__'8853''7496'__466 (coe d_pchainC_820 (coe v1))
            (coe
               d__'8853''7496'__466
               (coe
                  d__'8853''7496'__466
                  (\ v3 v4 ->
                     coe
                       du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                  (coe
                     d__'8853''7496'__466
                     (coe d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                     (coe d_'9251'_480)))
               (coe
                  d_pex_814 (coe (1 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_436
              (coe
                 MAlonzo.Code.Once.Format.Doc.C_group_34
                 (coe
                    MAlonzo.Code.Once.Format.Doc.C_nest_32
                    (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v3)))
              v5))
-- Once.Format.Print.pchainC
d_pchainC_820 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC_820 v0
  = let v1
          = d_pex_814
              (coe (1 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pchainC'8242'_822
                (coe d_isCompose_790 (coe d_headOf_794 (coe v2))) (coe v2) (coe v3)
         _ -> coe v1)
-- Once.Format.Print.pchainC′
d_pchainC'8242'_822 ::
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pchainC'8242'_822 v0 v1 v2
  = let v3
          = d_pcomp_816
              (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v1) (coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
                  -> coe
                       d__'8853''7496'__466 (coe d_pchainC_820 (coe v5))
                       (coe
                          d__'8853''7496'__466
                          (coe
                             d__'8853''7496'__466
                             (\ v6 v7 ->
                                coe
                                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v7)
                             (coe
                                d__'8853''7496'__466
                                (coe d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                                (coe d_'9251'_480)))
                          (coe
                             d_pex_814 (coe (1 :: Integer))
                             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)))
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.pbin
d_pbin_824 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pbin_824 v0 v1 v2 v3
  = coe
      d__'8853''7496'__466 (coe d_pleft_826 (coe v0) (coe v2))
      (coe
         d__'8853''7496'__466
         (\ v4 v5 ->
            coe
              du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v5)
         (coe
            d__'8853''7496'__466 (coe d_t_476 (coe d_opTok_776 (coe v1)))
            (coe
               d__'8853''7496'__466 (coe d_'9251'_480)
               (coe
                  d_pex_814 (coe addInt (coe (1 :: Integer)) (coe v0))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)))))
-- Once.Format.Print.pleft
d_pleft_826 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pleft_826 v0 v1
  = let v2
          = d_pex_814
              (coe d_leftLevel_802 (coe v0))
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe eqInt (coe v0) (coe d_opLevel_778 (coe v3)))
                   (coe ltInt (coe (1 :: Integer)) (coe v0)))
                (coe d_pbin_824 (coe v0) (coe v3) (coe v4) (coe v5))
                (coe
                   d_pex_814 (coe d_leftLevel_802 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1))
         _ -> coe v2)
-- Once.Format.Print.pspine
d_pspine_828 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine_828 v0
  = let v1
          = d_pex_814
              (coe (6 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
           -> coe
                d_pspine'8242'_830
                (coe d_isCompose_790 (coe d_headOf_794 (coe v2))) (coe v2) (coe v3)
         _ -> coe v1)
-- Once.Format.Print.pspine′
d_pspine'8242'_830 ::
  Bool ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pspine'8242'_830 v0 v1 v2
  = let v3
          = d__'8853''7496'__466
              (coe d_pspine_828 (coe v1))
              (coe
                 d__'8853''7496'__466
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                 (coe
                    d_pex_814 (coe (6 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
                  -> coe d_pcompose_818 (coe (6 :: Integer)) (coe v5) (coe v2)
                _ -> coe v3
         _ -> coe v3)
-- Once.Format.Print.plam
d_plam_832 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam_832 v0 v1
  = coe
      du__'62''62''61''8242'__446
      (coe
         d__'8853''7496'__466
         (coe
            d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLambda_38))
         (coe
            d__'8853''7496'__466 (coe d_word_500 (coe v0))
            (coe d_plam'8242'_834 (coe v1))))
      (coe
         (\ v2 v3 v4 ->
            coe
              du_pure'8242'_436
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v2)) v4))
-- Once.Format.Print.plam′
d_plam'8242'_834 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plam'8242'_834 v0
  = let v1
          = d__'8853''7496'__466
              (coe d_'9251'_480)
              (coe
                 d__'8853''7496'__466
                 (coe
                    d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                 (coe
                    du__'62''62''61''8242'__446
                    (coe
                       d__'8853''7496'__466
                       (\ v1 v2 ->
                          coe
                            du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v2)
                       (coe
                          d_pex_814 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0)))
                    (coe
                       (\ v1 v2 v3 ->
                          coe
                            du_pure'8242'_436
                            (coe
                               MAlonzo.Code.Once.Format.Doc.C_nest_32
                               (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v1))
                            v3)))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
           -> coe
                d__'8853''7496'__466 (coe d_'9251'_480)
                (coe
                   d__'8853''7496'__466 (coe d_word_500 (coe v2))
                   (coe d_plam'8242'_834 (coe v3)))
         _ -> coe v1)
-- Once.Format.Print.plet
d_plet_836 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet_836 v0 v1 v2
  = coe
      du__'62''62''61''8242'__446
      (coe d_plet'8242'_838 (coe v0) (coe v1) (coe v2))
      (coe
         (\ v3 v4 v5 ->
            coe
              du_pure'8242'_436
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v3)) v5))
-- Once.Format.Print.plet′
d_plet'8242'_838 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plet'8242'_838 v0 v1 v2
  = let v3
          = d__'8853''7496'__466
              (coe d_lhead_840 (coe v0) (coe v1))
              (coe
                 d__'8853''7496'__466
                 (\ v3 v4 ->
                    coe
                      du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                 (coe
                    d__'8853''7496'__466
                    (coe d_word_500 (coe ("in" :: Data.Text.Text)))
                    (coe
                       d__'8853''7496'__466 (coe d_'9251'_480)
                       (coe
                          d_pex_814 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v4 v5 v6
           -> coe
                d__'8853''7496'__466 (coe d_lhead_840 (coe v0) (coe v1))
                (coe
                   d__'8853''7496'__466
                   (\ v7 v8 ->
                      coe
                        du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v8)
                   (coe
                      d__'8853''7496'__466
                      (coe d_word_500 (coe ("in" :: Data.Text.Text)))
                      (coe
                         d__'8853''7496'__466 (coe d_'9251'_480)
                         (coe d_plet'8242'_838 (coe v4) (coe v5) (coe v6)))))
         _ -> coe v3)
-- Once.Format.Print.lhead
d_lhead_840 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lhead_840 v0 v1
  = coe
      d__'8853''7496'__466
      (coe d_word_500 (coe ("let" :: Data.Text.Text)))
      (coe
         d__'8853''7496'__466 (coe d_'9251'_480)
         (coe
            d__'8853''7496'__466 (coe d_word_500 (coe v0))
            (coe
               d__'8853''7496'__466 (coe d_'9251'_480)
               (coe
                  d__'8853''7496'__466
                  (coe
                     d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                  (coe
                     du__'62''62''61''8242'__446
                     (coe
                        d__'8853''7496'__466
                        (\ v2 v3 ->
                           coe
                             du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v3)
                        (coe
                           d_pex_814 (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v1)))
                     (coe
                        (\ v2 v3 v4 ->
                           coe
                             du_pure'8242'_436
                             (coe
                                MAlonzo.Code.Once.Format.Doc.C_group_34
                                (coe
                                   MAlonzo.Code.Once.Format.Doc.C_nest_32
                                   (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v2)))
                             v4)))))))
-- Once.Format.Print.pdes
d_pdes_842 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdes_842 v0 v1 v2 v3 v4
  = coe
      du__'62''62''61''8242'__446
      (coe
         d__'8853''7496'__466
         (coe d_word_500 (coe ("destruct" :: Data.Text.Text)))
         (coe
            d__'8853''7496'__466 (coe d_'9251'_480)
            (coe
               d__'8853''7496'__466
               (coe
                  d_pex_814 (coe (0 :: Integer))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0))
               (coe
                  d__'8853''7496'__466 (coe d_'9251'_480)
                  (coe
                     d__'8853''7496'__466
                     (coe d_word_500 (coe ("of" :: Data.Text.Text)))
                     (coe
                        du__'62''62''61''8242'__446
                        (coe
                           d__'8853''7496'__466
                           (\ v5 v6 ->
                              coe
                                du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v6)
                           (coe
                              d__'8853''7496'__466
                              (coe
                                 d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLBrace_22))
                              (coe
                                 d__'8853''7496'__466 (coe d_'9251'_480)
                                 (coe
                                    d__'8853''7496'__466
                                    (coe d_word_500 (coe ("Left" :: Data.Text.Text)))
                                    (coe
                                       d__'8853''7496'__466 (coe d_'9251'_480)
                                       (coe
                                          d__'8853''7496'__466 (coe d_word_500 (coe v1))
                                          (coe
                                             d__'8853''7496'__466
                                             (coe
                                                d_infixOp_610
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                                             (coe
                                                d__'8853''7496'__466
                                                (coe
                                                   d_pex_814 (coe (0 :: Integer))
                                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                   (coe v2))
                                                (coe
                                                   d__'8853''7496'__466
                                                   (\ v5 v6 ->
                                                      coe
                                                        du_pure'8242'_436
                                                        (coe MAlonzo.Code.Once.Format.Doc.C_line_22)
                                                        v6)
                                                   (coe
                                                      d__'8853''7496'__466
                                                      (coe
                                                         d_t_476
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Surface.Lexing.C_TSemicolon_42))
                                                      (coe
                                                         d__'8853''7496'__466 (coe d_'9251'_480)
                                                         (coe
                                                            d__'8853''7496'__466
                                                            (coe
                                                               d_word_500
                                                               (coe ("Right" :: Data.Text.Text)))
                                                            (coe
                                                               d__'8853''7496'__466
                                                               (coe d_'9251'_480)
                                                               (coe
                                                                  d__'8853''7496'__466
                                                                  (coe d_word_500 (coe v3))
                                                                  (coe
                                                                     d__'8853''7496'__466
                                                                     (coe
                                                                        d_infixOp_610
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30))
                                                                     (coe
                                                                        d__'8853''7496'__466
                                                                        (coe
                                                                           d_pex_814
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                                           (coe v4))
                                                                        (coe
                                                                           d__'8853''7496'__466
                                                                           (\ v5 v6 ->
                                                                              coe
                                                                                du_pure'8242'_436
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Format.Doc.C_line_22)
                                                                                v6)
                                                                           (coe
                                                                              d_t_476
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Surface.Lexing.C_TRBrace_24)))))))))))))))))))
                        (coe
                           (\ v5 v6 v7 ->
                              coe
                                du_pure'8242'_436
                                (coe
                                   MAlonzo.Code.Once.Format.Doc.C_nest_32
                                   (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v5))
                                v7))))))))
      (coe
         (\ v5 v6 v7 ->
            coe
              du_pure'8242'_436
              (coe MAlonzo.Code.Once.Format.Doc.C_group_34 (coe v5)) v7))
-- Once.Format.Print.path
d_path_1094 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path_1094 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe d_word_500 (coe v1)
             (:) v3 v4
               -> coe
                    d__'8853''7496'__466 (coe d_word_500 (coe v1))
                    (coe
                       d__'8853''7496'__466
                       (coe d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48))
                       (coe d_path_1094 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.spaced
d_spaced_1102 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spaced_1102 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 v2 ->
                coe
                  du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_empty_12) v2)
      (:) v1 v2
        -> coe
             d__'8853''7496'__466 (coe d_'9251'_480)
             (coe
                d__'8853''7496'__466 (coe d_word_500 (coe v1))
                (coe d_spaced_1102 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pbody
d_pbody_1108 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pbody_1108 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v1 v2
        -> coe
             d__'8853''7496'__466 (coe d_name_598 (coe v1))
             (coe
                d__'8853''7496'__466 (coe d_'9251'_480)
                (coe
                   d__'8853''7496'__466
                   (coe
                      d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                   (coe
                      d__'8853''7496'__466
                      (\ v3 v4 ->
                         coe
                           du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                      (coe
                         d_pty_614 (coe (0 :: Integer))
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v1 v2
        -> coe
             d__'8853''7496'__466 (coe d_name_598 (coe v1))
             (coe
                d__'8853''7496'__466
                (coe
                   d_spaced_1102
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_lams_780 (coe v2))))
                (coe
                   d__'8853''7496'__466 (coe d_'9251'_480)
                   (coe
                      d__'8853''7496'__466
                      (coe
                         d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                      (coe
                         d__'8853''7496'__466
                         (\ v3 v4 ->
                            coe
                              du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                         (coe
                            d_pex_814 (coe (0 :: Integer))
                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_lams_780 (coe v2))))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v1 v2
        -> coe
             d__'8853''7496'__466
             (coe d_word_500 (coe ("signature" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__466 (coe d_'9251'_480)
                (coe
                   d__'8853''7496'__466 (coe d_word_500 (coe v1))
                   (coe
                      d__'8853''7496'__466 (coe d_'9251'_480)
                      (coe
                         d__'8853''7496'__466
                         (coe
                            d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TColon_26))
                         (coe
                            d__'8853''7496'__466
                            (\ v3 v4 ->
                               coe
                                 du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22) v4)
                            (coe
                               d_pty_614 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v2)))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_118 v1 v2 v3
        -> coe
             d__'8853''7496'__466
             (coe d_word_500 (coe ("type" :: Data.Text.Text)))
             (coe
                d__'8853''7496'__466 (coe d_'9251'_480)
                (coe
                   d__'8853''7496'__466 (coe d_word_500 (coe v1))
                   (coe
                      d__'8853''7496'__466 (coe d_spaced_1102 (coe v2))
                      (coe
                         d__'8853''7496'__466 (coe d_'9251'_480)
                         (coe
                            d__'8853''7496'__466
                            (coe
                               d_t_476 (coe MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28))
                            (coe
                               d__'8853''7496'__466
                               (\ v4 v5 ->
                                  coe
                                    du_pure'8242'_436 (coe MAlonzo.Code.Once.Format.Doc.C_line_22)
                                    v5)
                               (coe
                                  d_pty_614 (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3))))))))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                      -> coe
                           d__'8853''7496'__466
                           (coe d_word_500 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__466 (coe d_'9251'_480)
                              (coe
                                 d__'8853''7496'__466 (coe d_path_1094 (coe v2))
                                 (coe
                                    d__'8853''7496'__466 (coe d_'9251'_480)
                                    (coe
                                       d__'8853''7496'__466
                                       (coe d_word_500 (coe ("as" :: Data.Text.Text)))
                                       (coe
                                          d__'8853''7496'__466 (coe d_'9251'_480)
                                          (coe d_word_500 (coe v4)))))))
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           d__'8853''7496'__466
                           (coe d_word_500 (coe ("import" :: Data.Text.Text)))
                           (coe
                              d__'8853''7496'__466 (coe d_'9251'_480) (coe d_path_1094 (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pdecl
d_pdecl_1134 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdecl_1134 v0
  = coe
      du__'62''62''61''8242'__446 (coe d_pbody_1108 (coe v0))
      (coe
         (\ v1 v2 v3 ->
            coe
              du_pure'8242'_436
              (coe
                 MAlonzo.Code.Once.Format.Doc.C_group_34
                 (coe
                    MAlonzo.Code.Once.Format.Doc.C_nest_32
                    (coe MAlonzo.Code.Once.Format.Doc.d_indent_8) (coe v1)))
              v3))
-- Once.Format.Print.together
d_together_1140 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 -> Bool
d_together_1140 v0 v1
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
-- Once.Format.Print.gap
d_gap_1146 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_gap_1146 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_together_1140 (coe v2) (coe v1))
             (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
             (coe MAlonzo.Code.Once.Format.Doc.C_blank_26)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.gapEnd
d_gapEnd_1154 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_gapEnd_1154 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Once.Format.Doc.C_blank_26
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Format.Doc.C_empty_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.lead
d_lead_1156 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_lead_1156 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe d_topDoc_548 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_hasComment_552 (coe v1))
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                (coe d_topDoc_548 (coe v1))
                (coe MAlonzo.Code.Once.Format.Doc.C_blank_26))
             (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.ending
d_ending_1162 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [T_Note_6] -> MAlonzo.Code.Once.Format.Doc.T_Doc_10
d_ending_1162 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_hasComment_552 (coe v1))
      (coe
         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
         (coe d_gapEnd_1154 (coe v0)) (coe d_topDoc_548 (coe v1)))
      (coe MAlonzo.Code.Once.Format.Doc.C_empty_12)
-- Once.Format.Print.pdecls
d_pdecls_1168 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pdecls_1168 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_ending_1162 (coe v0)
                (coe
                   d_topList_516 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v3))
                   (coe d_hoist_104 (coe v3) (coe v2))))
             (coe v3)
      (:) v4 v5
        -> coe
             du_at_1190 (coe v0) (coe v4) (coe v5) (coe v3)
             (coe d_hoist_104 (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._.at
d_at_1190 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_1190 v0 v1 v2 ~v3 v4 v5 = du_at_1190 v0 v1 v2 v4 v5
du_at_1190 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_1190 v0 v1 v2 v3 v4
  = coe
      du_decl_1198 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe d_pdecl_1134 v1 v4 v3)
-- Once.Format.Print._._.decl
d_decl_1198 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decl_1198 v0 v1 v2 ~v3 v4 v5 v6 = du_decl_1198 v0 v1 v2 v4 v5 v6
du_decl_1198 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decl_1198 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             du_rest_1208 (coe v0) (coe v1) (coe v3) (coe v4) (coe v6) (coe v7)
             (coe
                d_pdecls_1168
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)) (coe v2)
                (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print._._._.rest
d_rest_1208 ::
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
d_rest_1208 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_rest_1208 v0 v1 v4 v5 v6 v7 v8
du_rest_1208 ::
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Format.Doc.T_Doc_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rest_1208 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                (coe d_gap_1146 (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                   (coe
                      d_lead_1156 (coe v0)
                      (coe d_topList_516 (coe v2) (coe v5) (coe v3)))
                   (coe
                      MAlonzo.Code.Once.Format.Doc.C__'60''62'__30 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Format.Doc.C__'60''62'__30
                         (coe MAlonzo.Code.Once.Format.Doc.C_newline_24) (coe v7)))))
             (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.pmodule
d_pmodule_1214 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pmodule_1214 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_128 v1
        -> coe
             d_pdecls_1168 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Print.format
d_format_1218 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Once.Format.Lex.T_Item_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_format_1218 v0 v1
  = coe
      MAlonzo.Code.Once.Format.Doc.d_render_454
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_pmodule_1214 v0 (d_trivia_426 (coe v1)) (0 :: Integer)))
