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

module MAlonzo.Code.Once.TypeCheck.Unify where

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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Unify.Subst
d_Subst_6 :: ()
d_Subst_6 = erased
-- Once.TypeCheck.Unify.emptySubst
d_emptySubst_8 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptySubst_8 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Unify.singleSubst
d_singleSubst_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_singleSubst_10 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Unify.lookupSubst
d_lookupSubst_16 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_32
d_lookupSubst_16 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupSubst_16 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Unify.applySubst
d_applySubst_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32
d_applySubst_48 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_34 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_36 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__38
             (coe d_applySubst_48 (coe v0) (coe v2))
             (coe d_applySubst_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__40
             (coe d_applySubst_48 (coe v0) (coe v2))
             (coe d_applySubst_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
             (coe d_applySubst_48 (coe v0) (coe v2)) (coe v3)
             (coe d_applySubst_48 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_44
             (coe d_applySubst_48 (coe v0) (coe v2))
             (coe d_applySubst_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> coe
             MAlonzo.Code.Once.Type.C_Fix_46
             (coe d_applySubst_48 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Int_48 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_50 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_52 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe v1
      MAlonzo.Code.Once.Type.C_TVar_56 v2
        -> let v3 = d_lookupSubst_16 (coe v2) (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Unify.composeSubst
d_composeSubst_110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_composeSubst_110 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v2 ->
               case coe v2 of
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                   -> coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                        (coe d_applySubst_48 (coe v0) (coe v4))
                 _ -> MAlonzo.RTE.mazUnreachableError))
         (coe v1))
      (coe v0)
-- Once.TypeCheck.Unify.occurs
d_occurs_122 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Bool
d_occurs_122 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occurs_122 (coe v0) (coe v2))
             (coe d_occurs_122 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occurs_122 (coe v0) (coe v2))
             (coe d_occurs_122 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occurs_122 (coe v0) (coe v2))
             (coe d_occurs_122 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occurs_122 (coe v0) (coe v2))
             (coe d_occurs_122 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> coe d_occurs_122 (coe v0) (coe v2)
      MAlonzo.Code.Once.Type.C_Int_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Str_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Buffer_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_TVar_56 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe seq (coe v5) (coe v4)
                       else coe seq (coe v5) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Unify.UnifyResult
d_UnifyResult_182 = ()
data T_UnifyResult_182
  = C_unified_184 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] |
    C_failed_186 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Unify.unify
d_unify_188 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_UnifyResult_182
d_unify_188 v0 v1
  = let v2
          = let v2
                  = coe
                      C_failed_186
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Error.C_UnificationError_20 (coe v0)
                         (coe v1)) in
            coe
              (case coe v1 of
                 MAlonzo.Code.Once.Type.C_TVar_56 v3
                   -> let v4 = d_occurs_122 (coe v3) (coe v0) in
                      coe
                        (if coe v4
                           then coe
                                  C_failed_186
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v3)
                                     (coe v0))
                           else coe C_unified_184 (coe d_singleSubst_10 (coe v3) (coe v0)))
                 _ -> coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_34
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Unit_34
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Void_36
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Void_36
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v5 v6
                  -> let v7 = d_unify_188 (coe v3) (coe v5) in
                     coe
                       (case coe v7 of
                          C_unified_184 v8
                            -> let v9
                                     = d_unify_188
                                         (coe d_applySubst_48 (coe v8) (coe v4))
                                         (coe d_applySubst_48 (coe v8) (coe v6)) in
                               coe
                                 (case coe v9 of
                                    C_unified_184 v10
                                      -> coe
                                           C_unified_184 (coe d_composeSubst_110 (coe v10) (coe v8))
                                    C_failed_186 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failed_186 v8 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_56 v5
                  -> let v6 = d_occurs_122 (coe v5) (coe v0) in
                     coe
                       (if coe v6
                          then coe
                                 C_failed_186
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v5)
                                    (coe v0))
                          else coe C_unified_184 (coe d_singleSubst_10 (coe v5) (coe v0)))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__40 v5 v6
                  -> let v7 = d_unify_188 (coe v3) (coe v5) in
                     coe
                       (case coe v7 of
                          C_unified_184 v8
                            -> let v9
                                     = d_unify_188
                                         (coe d_applySubst_48 (coe v8) (coe v4))
                                         (coe d_applySubst_48 (coe v8) (coe v6)) in
                               coe
                                 (case coe v9 of
                                    C_unified_184 v10
                                      -> coe
                                           C_unified_184 (coe d_composeSubst_110 (coe v10) (coe v8))
                                    C_failed_186 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failed_186 v8 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_56 v5
                  -> let v6 = d_occurs_122 (coe v5) (coe v0) in
                     coe
                       (if coe v6
                          then coe
                                 C_failed_186
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v5)
                                    (coe v0))
                          else coe C_unified_184 (coe d_singleSubst_10 (coe v5) (coe v0)))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v6 v7 v8
                  -> let v9 = d_unify_188 (coe v3) (coe v6) in
                     coe
                       (case coe v9 of
                          C_unified_184 v10
                            -> let v11
                                     = d_unify_188
                                         (coe d_applySubst_48 (coe v10) (coe v5))
                                         (coe d_applySubst_48 (coe v10) (coe v8)) in
                               coe
                                 (case coe v11 of
                                    C_unified_184 v12
                                      -> coe
                                           C_unified_184
                                           (coe d_composeSubst_110 (coe v12) (coe v10))
                                    C_failed_186 v12 -> coe v11
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failed_186 v10 -> coe v9
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_56 v6
                  -> let v7 = d_occurs_122 (coe v6) (coe v0) in
                     coe
                       (if coe v7
                          then coe
                                 C_failed_186
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v6)
                                    (coe v0))
                          else coe C_unified_184 (coe d_singleSubst_10 (coe v6) (coe v0)))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Eff_44 v5 v6
                  -> let v7 = d_unify_188 (coe v3) (coe v5) in
                     coe
                       (case coe v7 of
                          C_unified_184 v8
                            -> let v9
                                     = d_unify_188
                                         (coe d_applySubst_48 (coe v8) (coe v4))
                                         (coe d_applySubst_48 (coe v8) (coe v6)) in
                               coe
                                 (case coe v9 of
                                    C_unified_184 v10
                                      -> coe
                                           C_unified_184 (coe d_composeSubst_110 (coe v10) (coe v8))
                                    C_failed_186 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failed_186 v8 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Type.C_TVar_56 v5
                  -> let v6 = d_occurs_122 (coe v5) (coe v0) in
                     coe
                       (if coe v6
                          then coe
                                 C_failed_186
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v5)
                                    (coe v0))
                          else coe C_unified_184 (coe d_singleSubst_10 (coe v5) (coe v0)))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Fix_46 v3
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Fix_46 v4
                  -> coe d_unify_188 (coe v3) (coe v4)
                MAlonzo.Code.Once.Type.C_TVar_56 v4
                  -> let v5 = d_occurs_122 (coe v4) (coe v0) in
                     coe
                       (if coe v5
                          then coe
                                 C_failed_186
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v4)
                                    (coe v0))
                          else coe C_unified_184 (coe d_singleSubst_10 (coe v4) (coe v0)))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Int_48
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Int_48
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Float_50
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Float_50
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Str_52
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Str_52
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Buffer_54
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Buffer_54
                  -> coe C_unified_184 (coe d_emptySubst_8)
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_TVar_56 v3
           -> let v4
                    = let v4 = d_occurs_122 (coe v3) (coe v1) in
                      coe
                        (if coe v4
                           then coe
                                  C_failed_186
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_OccursCheck_18 (coe v3)
                                     (coe v1))
                           else coe C_unified_184 (coe d_singleSubst_10 (coe v3) (coe v1))) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C_TVar_56 v5
                     -> let v6
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v6 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                                     (coe v5)) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe C_unified_184 (coe d_emptySubst_8))
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              C_unified_184
                                              (coe d_singleSubst_10 (coe v3) (coe v1)))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Unify.unifyResult
d_unifyResult_506 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_Result_48
d_unifyResult_506 v0 v1
  = let v2 = d_unify_188 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_unified_184 v3
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_ok_52 (coe v3)
         C_failed_186 v3
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_fail_54 (coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
