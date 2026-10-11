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
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Typing.Scope
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Context.∅
d_'8709'_6 :: [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8]
d_'8709'_6 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Context._,_∷_
d__'44'_'8759'__8 ::
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8]
d__'44'_'8759'__8 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Spec.Typing.Scope.C_mkBinding_22 (coe v1)
         (coe v2) (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14))
      (coe v0)
-- Once.TypeCheck.Context._,_∷_^_
d__'44'_'8759'_'94'__16 ::
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8]
d__'44'_'8759'_'94'__16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Spec.Typing.Scope.C_mkBinding_22 (coe v1)
         (coe v2) (coe v3))
      (coe v0)
-- Once.TypeCheck.Context.LookupResult
d_LookupResult_26 = ()
data T_LookupResult_26
  = C_found_34 MAlonzo.Code.Once.Spec.Type.T_Type_8
               MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 Integer |
    C_notFound_36
-- Once.TypeCheck.Context.lookup
d_lookup_38 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  T_LookupResult_26
d_lookup_38 v0 v1
  = case coe v1 of
      [] -> coe C_notFound_36
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
                        (coe MAlonzo.Code.Once.Spec.Typing.Scope.d_name_16 (coe v2))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe
                                 C_found_34
                                 (coe MAlonzo.Code.Once.Spec.Typing.Scope.d_type_18 (coe v2))
                                 (coe MAlonzo.Code.Once.Spec.Typing.Scope.d_quantity_20 (coe v2))
                                 (coe (0 :: Integer)))
                       else coe
                              seq (coe v6)
                              (let v7 = d_lookup_38 (coe v0) (coe v3) in
                               coe
                                 (case coe v7 of
                                    C_found_34 v8 v9 v10
                                      -> coe
                                           C_found_34 (coe v8) (coe v9)
                                           (coe addInt (coe (1 :: Integer)) (coe v10))
                                    C_notFound_36 -> coe v7
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context.isBound
d_isBound_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] -> Bool
d_isBound_86 v0 v1
  = let v2 = d_lookup_38 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_found_34 v3 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_notFound_36 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Context.ctxLength
d_ctxLength_104 ::
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] -> Integer
d_ctxLength_104 = coe MAlonzo.Code.Data.List.Base.du_length_268
-- Once.TypeCheck.Context.names
d_names_106 ::
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_106 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Typing.Scope.d_name_16 (coe v1))
             (coe d_names_106 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context._∈_at_⦂_
d__'8712'_at_'10626'__114 a0 a1 a2 a3 = ()
data T__'8712'_at_'10626'__114
  = C_here_124 | C_there_138 T__'8712'_at_'10626'__114
-- Once.TypeCheck.Context.lookupWithEvidence
d_lookupWithEvidence_148 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupWithEvidence_148 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Typing.Scope.C_mkBinding_22 v4 v5 v6
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
                                              (coe (0 :: Integer)) (coe C_here_124))))
                              else coe
                                     seq (coe v9)
                                     (let v10 = d_lookupWithEvidence_148 (coe v0) (coe v3) in
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
                                                                      (coe C_there_138 v15)))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Context.ctxTypes
d_ctxTypes_216 ::
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  [MAlonzo.Code.Once.Spec.Type.T_Type_8]
d_ctxTypes_216 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Typing.Scope.d_type_18 (coe v1))
             (coe d_ctxTypes_216 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
