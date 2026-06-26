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

module MAlonzo.Code.Once.Target.Symbol where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Target.Symbol.showNat
d_showNat_6 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showNat_6
  = coe
      MAlonzo.Code.Data.Nat.Show.du_showInBase_78 (coe (10 :: Integer))
-- Once.Target.Symbol.once-prefix
d_once'45'prefix_8 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_once'45'prefix_8 = coe ("once_" :: Data.Text.Text)
-- Once.Target.Symbol.z-encode-char-aux
d_z'45'encode'45'char'45'aux_12 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_z'45'encode'45'char'45'aux_12 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'z')
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'z')
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             else coe
                    seq (coe v9)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'z')
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'q')
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                              else coe
                                     seq (coe v11)
                                     (case coe v3 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe 'z')
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe 'p')
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                               else coe
                                                      seq (coe v13)
                                                      (case coe v4 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                           -> if coe v14
                                                                then coe
                                                                       seq (coe v15)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe 'z')
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe 't')
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                else coe
                                                                       seq (coe v15)
                                                                       (case coe v5 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                            -> if coe v16
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                           (coe 'z')
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                              (coe
                                                                                                 'b')
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (case coe
                                                                                                v6 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                             -> if coe
                                                                                                     v18
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               'z')
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  'h')
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (case coe
                                                                                                                 v7 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                              -> if coe
                                                                                                                      v20
                                                                                                                   then coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                             (coe
                                                                                                                                'z')
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                (coe
                                                                                                                                   'd')
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                             (coe
                                                                                                                                v0)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Symbol.z-encode-char
d_z'45'encode'45'char_30 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_z'45'encode'45'char_30 v0
  = coe
      d_z'45'encode'45'char'45'aux_12 (coe v0)
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'z'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
         (coe '\''))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '+'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '*'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '!'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '?'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '.'))
-- Once.Target.Symbol.z-encode
d_z'45'encode_34 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_z'45'encode_34 v0
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246
         (coe d_z'45'encode'45'char_30)
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Target.Symbol.mangle-component
d_mangle'45'component_38 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_mangle'45'component_38 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe
         d_showNat_6
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe
               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
               (d_z'45'encode_34 (coe v0)))))
      (d_z'45'encode_34 (coe v0))
-- Once.Target.Symbol.join-us
d_join'45'us_42 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_join'45'us_42 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe v1
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("_" :: Data.Text.Text) (d_join'45'us_42 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.Symbol.once-symbol-path
d_once'45'symbol'45'path_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_once'45'symbol'45'path_52 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_once'45'prefix_8
      (d_join'45'us_42
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe d_mangle'45'component_38)
            (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v0))))
-- Once.Target.Symbol.once-symbol-own
d_once'45'symbol'45'own_56 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_once'45'symbol'45'own_56 v0
  = coe
      d_once'45'symbol'45'path_52
      (coe
         MAlonzo.Code.Once.CanonicalName.C_canonical_10
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
