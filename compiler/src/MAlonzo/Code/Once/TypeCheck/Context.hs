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

module MAlonzo.Code.Once.TypeCheck.Context where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Context.∅
d_'8709'_8 ::
  Integer -> [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
d_'8709'_8 ~v0 = du_'8709'_8
du_'8709'_8 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
du_'8709'_8 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Context._,_∷_
d__'44'_'8759'__12 ::
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
d__'44'_'8759'__12 ~v0 v1 v2 v3 = du__'44'_'8759'__12 v1 v2 v3
du__'44'_'8759'__12 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
du__'44'_'8759'__12 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkBinding_26 (coe v1)
         (coe v2) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12))
      (coe v0)
-- Once.TypeCheck.Context._,_∷_^_
d__'44'_'8759'_'94'__22 ::
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
d__'44'_'8759'_'94'__22 ~v0 v1 v2 v3 v4
  = du__'44'_'8759'_'94'__22 v1 v2 v3 v4
du__'44'_'8759'_'94'__22 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10]
du__'44'_'8759'_'94'__22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkBinding_26 (coe v1)
         (coe v2) (coe v3))
      (coe v0)
-- Once.TypeCheck.Context.LookupResult
d_LookupResult_34 a0 = ()
data T_LookupResult_34
  = C_found_44 MAlonzo.Code.Once.Spec.Type.T_Ty_8
               MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 Integer |
    C_notFound_46
-- Once.TypeCheck.Context.lookup
d_lookup_50 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  T_LookupResult_34
d_lookup_50 ~v0 v1 v2 = du_lookup_50 v1 v2
du_lookup_50 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  T_LookupResult_34
du_lookup_50 v0 v1
  = case coe v1 of
      [] -> coe C_notFound_46
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_name_20 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe
                                 C_found_44
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_type_22 (coe v2))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.Scope.d_quantity_24 (coe v2))
                                 (coe (0 :: Integer)))
                       else coe
                              seq (coe v6)
                              (let v7 = coe du_lookup_50 (coe v0) (coe v3) in
                               coe
                                 (case coe v7 of
                                    C_found_44 v8 v9 v10
                                      -> coe
                                           C_found_44 (coe v8) (coe v9)
                                           (coe addInt (coe (1 :: Integer)) (coe v10))
                                    C_notFound_46 -> coe v7
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context.isBound
d_isBound_100 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] -> Bool
d_isBound_100 ~v0 v1 v2 = du_isBound_100 v1 v2
du_isBound_100 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] -> Bool
du_isBound_100 v0 v1
  = let v2 = coe du_lookup_50 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_found_44 v3 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_notFound_46 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Context.ctxLength
d_ctxLength_120 ::
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] -> Integer
d_ctxLength_120 ~v0 = du_ctxLength_120
du_ctxLength_120 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] -> Integer
du_ctxLength_120 = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.TypeCheck.Context.names
d_names_124 ::
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_124 ~v0 v1 = du_names_124 v1
du_names_124 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_names_124 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_name_20 (coe v1))
             (coe du_names_124 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context._∈_at_⦂_
d__'8712'_at_'10626'__134 a0 a1 a2 a3 a4 = ()
data T__'8712'_at_'10626'__134
  = C_here_146 | C_there_160 T__'8712'_at_'10626'__134
-- Once.TypeCheck.Context.lookupWithEvidence
d_lookupWithEvidence_172 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupWithEvidence_172 ~v0 v1 v2
  = du_lookupWithEvidence_172 v1 v2
du_lookupWithEvidence_172 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupWithEvidence_172 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Typing.Scope.C_mkBinding_26 v4 v5 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v7 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe (0 :: Integer)) (coe C_here_146))))
                              else coe
                                     seq (coe v9)
                                     (let v10 = coe du_lookupWithEvidence_172 (coe v0) (coe v3) in
                                      coe
                                        (case coe v10 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                             -> case coe v11 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                    -> case coe v13 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v12)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         addInt (coe (1 :: Integer))
                                                                         (coe v14))
                                                                      (coe C_there_160 v15)))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context.ctxTypes
d_ctxTypes_242 ::
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8]
d_ctxTypes_242 ~v0 v1 = du_ctxTypes_242 v1
du_ctxTypes_242 ::
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_10] ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8]
du_ctxTypes_242 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_type_22 (coe v1))
             (coe du_ctxTypes_242 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
