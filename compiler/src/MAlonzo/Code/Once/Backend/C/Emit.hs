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

module MAlonzo.Code.Once.Backend.C.Emit where

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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Backend.C.Emit.unlines
d_unlines_8 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_8 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_unlines_8 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.C.Emit.isSuffixOf
d_isSuffixOf_16 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_isSuffixOf_16 v0 v1
  = coe
      du_go_26 (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1)
-- Once.Backend.C.Emit._.go
d_go_26 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_go_26 ~v0 ~v1 v2 v3 = du_go_26 v2 v3
du_go_26 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
du_go_26 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             (:) v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased erased
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                               (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v2)
                               (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe du_go_26 (coe v3) (coe v5))
                              else coe seq (coe v8) (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.C.Emit.endsWith
d_endsWith_56 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_endsWith_56 v0 v1
  = coe
      d_isSuffixOf_16
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Backend.C.Emit.cTypeName
d_cTypeName_62 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cTypeName_62 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34 -> coe ("void*" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Void_36 -> coe ("void" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C__'42'__38 v1 v2
        -> coe ("OncePair" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C__'43'__40 v1 v2
        -> coe ("OnceSum" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v1 v2 v3
        -> coe ("void*" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Eff_44 v1 v2
        -> coe ("void*" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Fix_46 v1
        -> coe ("void*" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Int_48 -> coe ("int" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Float_50
        -> coe ("double" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Str_52
        -> coe ("OnceString" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_Buffer_54
        -> coe ("OnceBuffer" :: Data.Text.Text)
      MAlonzo.Code.Once.Type.C_TVar_56 v1
        -> coe ("void*" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.C.Emit.needsPairCast
d_needsPairCast_64 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_needsPairCast_64 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe d_endsWith_56 (coe v0) (coe (".fst" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe d_endsWith_56 (coe v0) (coe (".snd" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe d_endsWith_56 (coe v0) (coe (")->fst" :: Data.Text.Text)))
            (coe d_endsWith_56 (coe v0) (coe (")->snd" :: Data.Text.Text)))))
-- Once.Backend.C.Emit.pairAccess
d_pairAccess_68 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pairAccess_68 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_needsPairCast_64 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("((OncePair*)" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (")->" :: Data.Text.Text) v1)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("." :: Data.Text.Text) v1))
-- Once.Backend.C.Emit.escapeChar
d_escapeChar_74 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_escapeChar_74 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)) in
    coe
      (case coe v0 of
         '\t' -> coe ("\\t" :: Data.Text.Text)
         '\n' -> coe ("\\n" :: Data.Text.Text)
         '\r' -> coe ("\\r" :: Data.Text.Text)
         '"' -> coe ("\\\"" :: Data.Text.Text)
         '\\' -> coe ("\\\\" :: Data.Text.Text)
         _ -> coe v1)
-- Once.Backend.C.Emit.escapeString
d_escapeString_78 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_escapeString_78 v0
  = coe
      du_go_86
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Backend.C.Emit._.go
d_go_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_go_86 ~v0 v1 = du_go_86 v1
du_go_86 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_go_86 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_escapeChar_74 (coe v1)) (coe du_go_86 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.C.Emit.functionDecl
d_functionDecl_92 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionDecl_92 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              ("void* once_" :: Data.Text.Text)
              (coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                 ("(void)" :: Data.Text.Text)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_cTypeName_62 (coe v5))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" once_" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_cTypeName_62 (coe v3)) (" x)" :: Data.Text.Text)))))
         MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_cTypeName_62 (coe v4))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" once_" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("(" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_cTypeName_62 (coe v3)) (" x)" :: Data.Text.Text)))))
         _ -> coe v2)
