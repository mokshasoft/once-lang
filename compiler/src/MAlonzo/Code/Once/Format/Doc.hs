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

module MAlonzo.Code.Once.Format.Doc where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Format.Spell
import qualified MAlonzo.Code.Once.Spec.Surface.Lexing
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Format.Doc.width
d_width_6 :: Integer
d_width_6 = coe (100 :: Integer)
-- Once.Format.Doc.indent
d_indent_8 :: Integer
d_indent_8 = coe (2 :: Integer)
-- Once.Format.Doc.Doc
d_Doc_10 = ()
data T_Doc_10
  = C_empty_12 |
    C_tk_14 MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 | C_sp_16 |
    C_cmt_18 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_para_20 [MAlonzo.Code.Agda.Builtin.String.T_String_6] |
    C_line_22 | C_newline_24 | C_blank_26 |
    C_eol_28 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C__'60''62'__30 T_Doc_10 T_Doc_10 | C_nest_32 Integer T_Doc_10 |
    C_group_34 T_Doc_10
-- Once.Format.Doc.continues
d_continues_36 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_continues_36 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TInt_12 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TFloat_14 v2 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TBang_52
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOp_54 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> coe v1
                _ -> coe v1
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOpD_56 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Doc.dashes
d_dashes_38 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_dashes_38 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TArrow_30
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOp_54 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> coe v1
                _ -> coe v1
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOpD_56 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Doc.greater
d_greater_40 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_greater_40 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOp_54 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> coe v1
                _ -> coe v1
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOpD_56 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Doc.equals
d_equals_42 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_equals_42 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOp_54 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v3
                  -> case coe v3 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26
                         -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                       _ -> coe v1
                _ -> coe v1
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOpD_56 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Doc.dots
d_dots_44 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_dots_44 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Doc.number
d_number_46 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_number_46 v0
  = let v1 = d_continues_36 (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TDot_48
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Format.Doc.body
d_body_50 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_body_50 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ') (coe v0) in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v3 of
                (:) v4 v5
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v2)
                                (coe '-')))
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v4)
                                (coe '-'))))
                       (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ') (coe v0))
                _ -> coe v1
         _ -> coe v1)
-- Once.Format.Doc.Lexeme
d_Lexeme_60 = ()
data T_Lexeme_60
  = C_lt_62 MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 |
    C_lsp_64 | C_lnl_66 | C_lind_68 Integer |
    C_lcm_70 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
-- Once.Format.Doc.chars
d_chars_72 ::
  T_Lexeme_60 -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_chars_72 v0
  = case coe v0 of
      C_lt_62 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
             (MAlonzo.Code.Once.Format.Spell.d_spell_44 (coe v1))
      C_lsp_64
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C_lnl_66
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n')
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C_lind_68 v1
        -> coe
             MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v1) (coe ' ')
      C_lcm_70 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.apart
d_apart_80 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 -> Bool
d_apart_80 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TWord_10 v3
           -> coe d_continues_36 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TInt_12 v3
           -> coe d_number_46 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TFloat_14 v3 v4 v5
           -> coe d_number_46 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TLBrace_22
           -> coe d_dashes_38 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TEquals_28
           -> coe d_equals_42 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TBang_52
           -> coe d_equals_42 (coe v1)
         MAlonzo.Code.Once.Spec.Surface.Lexing.C_TOp_54 v3
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Surface.Operator.C_'8249'_'8250'_32 v4
                  -> case coe v4 of
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'43'_10
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'45'_12
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_dashes_38 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe d_greater_40 (coe v1)) (coe d_dots_44 (coe v1)))
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'42'_14
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'47'_16
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60'_18
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_equals_42 (coe v1)) (coe d_dots_44 (coe v1))
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'60''61'_20
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62'_22
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                              (coe d_equals_42 (coe v1)) (coe d_dots_44 (coe v1))
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'62''61'_24
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'61''61'_26
                         -> coe d_dots_44 (coe v1)
                       MAlonzo.Code.Once.Spec.Surface.Operator.C_o'33''61'_28
                         -> coe d_dots_44 (coe v1)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         _ -> coe v2)
-- Once.Format.Doc.oneLine
d_oneLine_114 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_oneLine_114 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                   (coe
                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                      (coe '\n')))
                (coe ' ') (coe v1))
             (coe d_oneLine_114 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.lineComment
d_lineComment_120 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_lineComment_120 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
         (coe d_oneLine_114 (coe d_body_50 (coe v0))))
-- Once.Format.Doc.flatWidth
d_flatWidth_124 :: T_Doc_10 -> Integer
d_flatWidth_124 v0
  = case coe v0 of
      C_empty_12 -> coe (0 :: Integer)
      C_tk_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d_length_22
             (coe MAlonzo.Code.Once.Format.Spell.d_spell_44 (coe v1))
      C_sp_16 -> coe (1 :: Integer)
      C_cmt_18 v1 -> coe (0 :: Integer)
      C_para_20 v1 -> coe (0 :: Integer)
      C_line_22 -> coe (1 :: Integer)
      C_newline_24 -> coe (0 :: Integer)
      C_blank_26 -> coe (0 :: Integer)
      C_eol_28 v1 -> coe (0 :: Integer)
      C__'60''62'__30 v1 v2
        -> coe
             addInt (coe d_flatWidth_124 (coe v1))
             (coe d_flatWidth_124 (coe v2))
      C_nest_32 v1 v2 -> coe d_flatWidth_124 (coe v2)
      C_group_34 v1 -> coe d_flatWidth_124 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St
d_St_136 = ()
data T_St_136
  = C_st_154 [T_Lexeme_60] Integer (Maybe Integer)
             [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Format.Doc.St.out
d_out_146 :: T_St_136 -> [T_Lexeme_60]
d_out_146 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.col
d_col_148 :: T_St_136 -> Integer
d_col_148 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.pend
d_pend_150 :: T_St_136 -> Maybe Integer
d_pend_150 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.ends
d_ends_152 ::
  T_St_136 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ends_152 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.column
d_column_156 :: T_St_136 -> Integer
d_column_156 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v5
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.put
d_put_162 :: T_Lexeme_60 -> Integer -> T_St_136 -> T_St_136
d_put_162 v0 v1 v2
  = case coe v2 of
      C_st_154 v3 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> coe
                    C_st_154
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_lind_68 (coe v7)) (coe v3)))
                    (coe addInt (coe v1) (coe v7))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v6)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    C_st_154
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3))
                    (coe addInt (coe v1) (coe v4)) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.space
d_space_186 :: T_St_136 -> T_St_136
d_space_186 v0
  = case coe v0 of
      C_st_154 v1 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v0
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe d_put_162 (coe C_lsp_64) (coe (1 :: Integer)) (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.token
d_token_202 ::
  MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8 ->
  T_St_136 -> T_St_136
d_token_202 v0 v1
  = case coe v1 of
      C_st_154 v2 v3 v4 v5
        -> let v6
                 = d_put_162
                     (coe C_lt_62 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d_length_22
                        (coe MAlonzo.Code.Once.Format.Spell.d_spell_44 (coe v0)))
                     (coe v1) in
           coe
             (case coe v2 of
                (:) v7 v8
                  -> case coe v7 of
                       C_lt_62 v9
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                     (coe d_apart_80 (coe v9) (coe v0))
                                     (coe
                                        d_put_162 (coe C_lt_62 (coe v0))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d_length_22
                                           (coe MAlonzo.Code.Once.Format.Spell.d_spell_44 (coe v0)))
                                        (coe d_space_186 (coe v1)))
                                     (coe
                                        d_put_162 (coe C_lt_62 (coe v0))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d_length_22
                                           (coe MAlonzo.Code.Once.Format.Spell.d_spell_44 (coe v0)))
                                        (coe v1))
                              _ -> coe v6
                       _ -> coe v6
                _ -> coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.joined
d_joined_218 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_joined_218 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v2 of
             []
               -> coe
                    d_lineComment_120
                    (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_lineComment_120
                       (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
                       (coe d_joined_218 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.trim
d_trim_226 :: [T_Lexeme_60] -> [T_Lexeme_60]
d_trim_226 v0
  = case coe v0 of
      (:) v1 v2
        -> case coe v1 of
             C_lsp_64 -> coe d_trim_226 (coe v2)
             _ -> coe v0
      _ -> coe v0
-- Once.Format.Doc.brk
d_brk_232 :: Integer -> T_St_136 -> T_St_136
d_brk_232 v0 v1
  = case coe v1 of
      C_st_154 v2 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> case coe v5 of
                    []
                      -> coe
                           C_st_154 (coe v2) (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v5)
                    (:) v7 v8
                      -> coe
                           C_st_154
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_lnl_66)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe C_lcm_70 (coe d_joined_218 (coe v5)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe C_lind_68 (coe v6)) (coe v2))))
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v5 of
                    []
                      -> coe
                           C_st_154
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_lnl_66)
                              (coe d_trim_226 (coe v2)))
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v5)
                    (:) v6 v7
                      -> coe
                           C_st_154
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_lnl_66)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe C_lcm_70 (coe d_joined_218 (coe v5)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_lsp_64)
                                    (coe d_trim_226 (coe v2)))))
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.comment
d_comment_264 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_St_136 -> T_St_136
d_comment_264 v0 v1 v2
  = case coe v2 of
      C_st_154 v3 v4 v5 v6
        -> coe
             d_brk_232 (coe v0)
             (coe
                C_st_154 (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.blankLine
d_blankLine_278 :: Integer -> T_St_136 -> T_St_136
d_blankLine_278 v0 v1
  = coe du_after_288 (coe v0) (coe d_brk_232 (coe v0) (coe v1))
-- Once.Format.Doc._.after
d_after_288 :: Integer -> T_St_136 -> T_St_136 -> T_St_136
d_after_288 v0 ~v1 v2 = du_after_288 v0 v2
du_after_288 :: Integer -> T_St_136 -> T_St_136
du_after_288 v0 v1
  = case coe v1 of
      C_st_154 v2 v3 v4 v5
        -> case coe v2 of
             []
               -> coe
                    C_st_154 (coe v2) (coe (0 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v5)
             (:) v6 v7
               -> coe
                    C_st_154
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_lnl_66)
                       (coe v2))
                    (coe (0 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.fill
d_fill_306 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [[MAlonzo.Code.Agda.Builtin.String.T_String_6]]
d_fill_306 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v3)
             (:) v4 v5
               -> coe
                    d_fill_306 (coe v0)
                    (coe
                       addInt
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v4)))
                       (coe v1))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2) (coe v3)
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v6)))
                          (coe v1))
                       (coe d_width_6))
                    (coe
                       d_fill_306 (coe v0)
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v6)))
                          (coe v1))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6) (coe v2))
                       (coe v7))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2)
                       (coe
                          d_fill_306 (coe v0)
                          (coe
                             addInt
                             (coe
                                addInt (coe (3 :: Integer))
                                (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v6)))
                             (coe v0))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.dashed
d_dashed_336 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_dashed_336 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '-')
         (coe
            MAlonzo.Code.Data.List.Base.du_concatMap_246
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ')
                    (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)))
            (coe v0)))
-- Once.Format.Doc.paragraph
d_paragraph_342 ::
  Integer ->
  [[MAlonzo.Code.Agda.Builtin.String.T_String_6]] ->
  T_St_136 -> T_St_136
d_paragraph_342 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             d_paragraph_342 (coe v0) (coe v4)
             (coe
                d_comment_264 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                   (d_dashed_336 (coe v3)))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.fits
d_fits_356 :: Integer -> Integer -> Bool
d_fits_356 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
      (coe addInt (coe v0) (coe v1)) (coe d_width_6)
-- Once.Format.Doc.layout
d_layout_362 :: Integer -> Bool -> T_Doc_10 -> T_St_136 -> T_St_136
d_layout_362 v0 v1 v2 v3
  = case coe v2 of
      C_empty_12 -> coe v3
      C_tk_14 v4 -> coe d_token_202 (coe v4) (coe v3)
      C_sp_16 -> coe d_space_186 (coe v3)
      C_cmt_18 v4 -> coe d_comment_264 (coe v0) (coe v4) (coe v3)
      C_para_20 v4
        -> coe
             d_paragraph_342 (coe v0)
             (coe
                d_fill_306 (coe v0)
                (coe addInt (coe (2 :: Integer)) (coe d_column_156 (coe v3)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4))
             (coe v3)
      C_line_22
        -> if coe v1
             then coe d_space_186 (coe v3)
             else coe d_brk_232 (coe v0) (coe v3)
      C_newline_24 -> coe d_brk_232 (coe v0) (coe v3)
      C_blank_26
        -> case coe v0 of
             0 -> coe d_blankLine_278 (coe (0 :: Integer)) (coe v3)
             _ -> coe d_brk_232 (coe v0) (coe v3)
      C_eol_28 v4
        -> case coe v3 of
             C_st_154 v5 v6 v7 v8
               -> coe
                    C_st_154 (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'60''62'__30 v4 v5
        -> coe
             d_layout_362 (coe v0) (coe v1) (coe v5)
             (coe d_layout_362 (coe v0) (coe v1) (coe v4) (coe v3))
      C_nest_32 v4 v5
        -> coe
             d_layout_362 (coe addInt (coe v0) (coe v4)) (coe v1) (coe v5)
             (coe v3)
      C_group_34 v4
        -> if coe v1
             then coe d_layout_362 (coe v0) (coe v1) (coe v4) (coe v3)
             else coe
                    d_layout_362 (coe v0)
                    (coe
                       d_fits_356 (coe d_column_156 (coe v3))
                       (coe d_flatWidth_124 (coe v4)))
                    (coe v4) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.lexemes
d_lexemes_470 :: T_Doc_10 -> [T_Lexeme_60]
d_lexemes_470 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_out_146
         (coe
            d_brk_232 (coe (0 :: Integer))
            (coe
               d_layout_362 (coe (0 :: Integer))
               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0)
               (coe
                  C_st_154 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                  (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.Format.Doc.render
d_render_474 ::
  T_Doc_10 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_render_474 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe d_chars_72)
         (coe d_lexemes_470 (coe v0)))
-- Once.Format.Doc.toks
d_toks_478 ::
  T_Doc_10 ->
  [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8] ->
  [MAlonzo.Code.Once.Spec.Surface.Lexing.T_Token_8]
d_toks_478 v0 v1
  = case coe v0 of
      C_empty_12 -> coe v1
      C_tk_14 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      C_sp_16 -> coe v1
      C_cmt_18 v2 -> coe v1
      C_para_20 v2 -> coe v1
      C_line_22 -> coe v1
      C_newline_24 -> coe v1
      C_blank_26 -> coe v1
      C_eol_28 v2 -> coe v1
      C__'60''62'__30 v2 v3
        -> coe d_toks_478 (coe v2) (coe d_toks_478 (coe v3) (coe v1))
      C_nest_32 v2 v3 -> coe d_toks_478 (coe v3) (coe v1)
      C_group_34 v2 -> coe d_toks_478 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
