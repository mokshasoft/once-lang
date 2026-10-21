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

module MAlonzo.Code.Once.Lang.Name where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Name.showCanonical
d_showCanonical_6 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCanonical_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> case coe v1 of
             [] -> coe ("" :: Data.Text.Text)
             (:) v2 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("." :: Data.Text.Text)
                               (d_showCanonical_6
                                  (coe MAlonzo.Code.Once.Spec.Name.C_canonical_12 (coe v3)))) in
                  coe
                    (case coe v3 of
                       [] -> coe v2
                       _ -> coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Name.noDotB
d_noDotB_14 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_noDotB_14 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe
                   MAlonzo.Code.Data.Char.Base.d__'8776''7495'__14 (coe v1)
                   (coe '.')))
             (coe d_noDotB_14 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Name.wordCharsB
d_wordCharsB_20 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_wordCharsB_20 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2 -> coe d_noDotB_14 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Name.wordB
d_wordB_26 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_wordB_26 v0
  = coe
      d_wordCharsB_20
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Lang.Name.wordsB
d_wordsB_30 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_wordsB_30 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe d_wordB_26 (coe v1))
             (coe d_wordsB_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Name.wordNameB
d_wordNameB_36 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Bool
d_wordNameB_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> coe d_wordsB_30 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Name.WordName
d_WordName_40 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> ()
d_WordName_40 = erased
