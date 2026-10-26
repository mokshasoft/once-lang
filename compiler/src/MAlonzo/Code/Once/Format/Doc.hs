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
    C_text_14 MAlonzo.Code.Agda.Builtin.String.T_String_6 | C_line_16 |
    C_newline_18 | C_blank_20 |
    C_eol_22 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C__'60''62'__24 T_Doc_10 T_Doc_10 | C_nest_26 Integer T_Doc_10 |
    C_group_28 T_Doc_10
-- Once.Format.Doc._<+>_
d__'60''43''62'__30 :: T_Doc_10 -> T_Doc_10 -> T_Doc_10
d__'60''43''62'__30 v0 v1
  = coe
      C__'60''62'__24 (coe v0)
      (coe
         C__'60''62'__24 (coe C_text_14 (coe (" " :: Data.Text.Text)))
         (coe v1))
-- Once.Format.Doc.sep
d_sep_36 :: [T_Doc_10] -> T_Doc_10
d_sep_36 v0
  = case coe v0 of
      [] -> coe C_empty_12
      (:) v1 v2
        -> coe C__'60''62'__24 (coe v1) (coe du_sep'45'rest_46 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc._.sep-rest
d_sep'45'rest_46 ::
  T_Doc_10 -> [T_Doc_10] -> [T_Doc_10] -> T_Doc_10
d_sep'45'rest_46 ~v0 ~v1 v2 = du_sep'45'rest_46 v2
du_sep'45'rest_46 :: [T_Doc_10] -> T_Doc_10
du_sep'45'rest_46 v0
  = case coe v0 of
      [] -> coe C_empty_12
      (:) v1 v2
        -> coe
             C__'60''62'__24 (coe C_line_16)
             (coe C__'60''62'__24 (coe v1) (coe du_sep'45'rest_46 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.flatWidth
d_flatWidth_52 :: T_Doc_10 -> Maybe Integer
d_flatWidth_52 v0
  = case coe v0 of
      C_empty_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
      C_text_14 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v1))
      C_line_16
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (1 :: Integer))
      C_newline_18 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_blank_20 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_eol_22 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
      C__'60''62'__24 v1 v2
        -> coe
             du_plus_64 (coe d_flatWidth_52 (coe v1))
             (coe d_flatWidth_52 (coe v2))
      C_nest_26 v1 v2 -> coe d_flatWidth_52 (coe v2)
      C_group_28 v1 -> coe d_flatWidth_52 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc._.plus
d_plus_64 ::
  T_Doc_10 ->
  T_Doc_10 -> Maybe Integer -> Maybe Integer -> Maybe Integer
d_plus_64 ~v0 ~v1 v2 v3 = du_plus_64 v2 v3
du_plus_64 :: Maybe Integer -> Maybe Integer -> Maybe Integer
du_plus_64 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe addInt (coe v2) (coe v3))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St
d_St_74 = ()
data T_St_74
  = C_st_92 [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] Integer
            (Maybe Integer) [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Format.Doc.St.out
d_out_84 :: T_St_74 -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_out_84 v0
  = case coe v0 of
      C_st_92 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.col
d_col_86 :: T_St_74 -> Integer
d_col_86 v0
  = case coe v0 of
      C_st_92 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.pend
d_pend_88 :: T_St_74 -> Maybe Integer
d_pend_88 v0
  = case coe v0 of
      C_st_92 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.St.ends
d_ends_90 ::
  T_St_74 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ends_90 v0
  = case coe v0 of
      C_st_92 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.emit
d_emit_94 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_St_74 -> T_St_74
d_emit_94 v0 v1
  = case coe v1 of
      C_st_92 v2 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> coe
                    C_st_92
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_reverse_444
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du_reverse_444
                             (coe
                                MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v6) (coe ' ')))
                          (coe v2)))
                    (coe
                       addInt (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v0))
                       (coe v6))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v5)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    C_st_92
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_reverse_444
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
                       (coe v2))
                    (coe
                       addInt (coe MAlonzo.Code.Data.String.Base.d_length_22 (coe v0))
                       (coe v3))
                    (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.flush
d_flush_114 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_flush_114 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_flush_114 (coe v3)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_reverse_444
                   (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe ' ') (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.trim
d_trim_124 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_trim_124 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1)
                   (coe ' ')))
             (coe d_trim_124 (coe v2)) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.brk
d_brk_130 :: Integer -> T_St_74 -> T_St_74
d_brk_130 v0 v1
  = case coe v1 of
      C_st_92 v2 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> case coe v5 of
                    []
                      -> coe
                           C_st_92 (coe v2) (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v5)
                    (:) v7 v8
                      -> coe
                           C_st_92
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n')
                              (coe
                                 d_flush_114 (coe v8)
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_reverse_444
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                          v7))
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_reverse_444
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v6)
                                             (coe ' ')))
                                       (coe v2)))))
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    C_st_92
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n')
                       (coe d_flush_114 (coe v5) (coe d_trim_124 (coe v2))))
                    (coe (0 :: Integer))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.blankLine
d_blankLine_158 :: Integer -> T_St_74 -> T_St_74
d_blankLine_158 v0 v1
  = let v2 = d_brk_130 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_st_92 v3 v4 v5 v6
           -> case coe v3 of
                []
                  -> coe
                       C_st_92 (coe v3) (coe (0 :: Integer))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v6)
                (:) v7 v8
                  -> coe
                       C_st_92
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '\n') (coe v3))
                       (coe (0 :: Integer))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Format.Doc.fits
d_fits_192 :: Integer -> Maybe Integer -> Bool
d_fits_192 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe addInt (coe v0) (coe v2)) (coe d_width_6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.layout
d_layout_200 :: Integer -> Bool -> T_Doc_10 -> T_St_74 -> T_St_74
d_layout_200 v0 v1 v2 v3
  = case coe v2 of
      C_empty_12 -> coe v3
      C_text_14 v4 -> coe d_emit_94 (coe v4) (coe v3)
      C_line_16
        -> if coe v1
             then coe d_emit_94 (coe (" " :: Data.Text.Text)) (coe v3)
             else coe d_brk_130 (coe v0) (coe v3)
      C_newline_18 -> coe d_brk_130 (coe v0) (coe v3)
      C_blank_20 -> coe d_blankLine_158 (coe v0) (coe v3)
      C_eol_22 v4
        -> case coe v3 of
             C_st_92 v5 v6 v7 v8
               -> coe
                    C_st_92 (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'60''62'__24 v4 v5
        -> coe
             d_layout_200 (coe v0) (coe v1) (coe v5)
             (coe d_layout_200 (coe v0) (coe v1) (coe v4) (coe v3))
      C_nest_26 v4 v5
        -> coe
             d_layout_200 (coe addInt (coe v0) (coe v4)) (coe v1) (coe v5)
             (coe v3)
      C_group_28 v4
        -> if coe v1
             then coe d_layout_200 (coe v0) (coe v1) (coe v4) (coe v3)
             else coe
                    d_layout_200 (coe v0)
                    (coe
                       d_fits_192 (coe du_column_286 (coe v3))
                       (coe d_flatWidth_52 (coe v4)))
                    (coe v4) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc._.column
d_column_286 ::
  Integer -> T_Doc_10 -> T_St_74 -> T_St_74 -> Integer
d_column_286 ~v0 ~v1 ~v2 v3 = du_column_286 v3
du_column_286 :: T_St_74 -> Integer
du_column_286 v0
  = case coe v0 of
      C_st_92 v1 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v5
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Format.Doc.render
d_render_292 ::
  T_Doc_10 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_render_292 v0
  = let v1
          = d_brk_130
              (coe (0 :: Integer))
              (coe
                 d_layout_200 (coe (0 :: Integer))
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0)
                 (coe
                    C_st_92 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    (coe (0 :: Integer))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
    coe
      (case coe v1 of
         C_st_92 v2 v3 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
