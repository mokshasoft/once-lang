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

module MAlonzo.Code.Once.Parser.Module.Resolve where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Generators
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.ResolvedRefs
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Generators
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Parser.Module.Resolve._._∈?_
d__'8712''63'__10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__10
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Parser.Module.Resolve.ModuleMap
d_ModuleMap_12 :: ()
d_ModuleMap_12 = erased
-- Once.Parser.Module.Resolve._path≟_
d__path'8799'__14 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d__path'8799'__14 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             (:) v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             (:) v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe d__path'8799'__14 (coe v3) (coe v5))
                              else coe seq (coe v8) (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupModule
d_lookupModule_44 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_64
d_lookupModule_44 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d__path'8799'__14 (coe v4) (coe v1) in
                  coe
                    (if coe v6
                       then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       else coe d_lookupModule_44 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.showPath
d_showPath_74 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPath_74 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("." :: Data.Text.Text) (d_showPath_74 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.AliasMap
d_AliasMap_82 :: ()
d_AliasMap_82 = erased
-- Once.Parser.Module.Resolve.collectAliases
d_collectAliases_84 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectAliases_84 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_collectAliases_84 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 v4
                  -> case coe v4 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_50 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v5))
                                     (coe d_collectAliases_84 (coe v2))
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupImportAlias
d_lookupImportAlias_94 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lookupImportAlias_94 v0 v1
  = case coe v0 of
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
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe
                                     seq (coe v8) (coe d_lookupImportAlias_94 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.UnaliasedMap
d_UnaliasedMap_124 :: ()
d_UnaliasedMap_124 = erased
-- Once.Parser.Module.Resolve.sigNames
d_sigNames_126 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sigNames_126 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_sigNames_126 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_58 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_sigNames_126 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.collectUnaliased
d_collectUnaliased_134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectUnaliased_134 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_collectUnaliased_134 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_50 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v8 = d_lookupModule_44 (coe v0) (coe v6) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_70 v10
                                                 -> coe
                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du_map_22
                                                         (coe
                                                            (\ v11 ->
                                                               coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v11) (coe v6)))
                                                         (coe d_sigNames_126 (coe v10)))
                                                      (coe d_collectUnaliased_134 (coe v0) (coe v3))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe d_collectUnaliased_134 (coe v0) (coe v3)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupUnaliased
d_lookupUnaliased_166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lookupUnaliased_166 v0 v1
  = case coe v0 of
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
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupUnaliased_166 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.expandPath
d_expandPath_196 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_expandPath_196 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("I" :: Data.Text.Text))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe ("Interpretations" :: Data.Text.Text)) (coe v2))
                       else coe seq (coe v5) (coe v0)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.canonVar
d_canonVar_214 ::
  Bool ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8
d_canonVar_214 v0 v1 v2 v3
  = if coe v0
      then coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_10 (coe v3)
      else (case coe v1 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 (coe v4)
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                -> case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                       -> coe
                            MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe d_expandPath_196 (coe v4))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14
                            (coe
                               MAlonzo.Code.Once.Spec.Name.C_canonical_12
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.Resolve.canonExpr
d_canonExpr_228 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8
d_canonExpr_228 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_10 v4
        -> coe
             d_canonVar_214
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
                   (coe
                      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                   (coe v4) (coe v0)))
             (coe MAlonzo.Code.Once.Generators.d_fromWord_74 (coe v4))
             (coe d_lookupUnaliased_166 (coe v1) (coe v4)) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_12 v4 v5
        -> let v6
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v5))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                        (coe ("this" :: Data.Text.Text))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe
                              seq (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14
                                 (coe
                                    MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                       else coe
                              seq (coe v8)
                              (let v9 = d_lookupImportAlias_94 (coe v2) (coe v5) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14
                                           (coe
                                              MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                 (coe d_expandPath_196 (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14
                                           (coe
                                              MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14 v4 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 v4 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_18 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_18
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_20 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_20 (coe v4)
             (coe
                d_canonExpr_228
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_22 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_22 (coe v4)
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe
                d_canonExpr_228
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_24 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_24
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_26 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_26
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
             (coe
                d_canonExpr_228
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v0))
                (coe v1) (coe v2) (coe v6))
             (coe v7)
             (coe
                d_canonExpr_228
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v0))
                (coe v1) (coe v2) (coe v8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_28 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_30 v4 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_32 v4 v5 v6 v7
        -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_34 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_34
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_36 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_36 (coe v4)
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_38 v4
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_38
             (coe d_canonExpr_228 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-canon
d_cls'45'canon_438 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_6
d_cls'45'canon_438 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_10
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_10 v6
               -> let v7
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                               (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v6))
                               (coe v0)) in
                  coe
                    (let v8 = d_lookupUnaliased_166 (coe v1) (coe v6) in
                     coe
                       (if coe v7
                          then coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_10
                          else (let v9
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.Any.du_fromSum_132)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.Any.du_toSum_126)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v9 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Surface.Generators.C_id_10)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe 'i')
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe 'd')
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                      v6)))
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                                                (coe
                                                   (\ v9 ->
                                                      MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46
                                                           (coe v9))
                                                        (coe v6)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Surface.Generators.C_terminal_18)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Surface.Generators.C_apply_30)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Spec.Surface.Generators.C_curry_32)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Spec.Surface.Generators.C_In_34)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Spec.Surface.Generators.C_Out_38)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Spec.Surface.Generators.C_ana_40)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Spec.Surface.Generators.C_unit_42)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Spec.Surface.Generators.C_toFloat_44)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))) in
                                coe
                                  (case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                       -> if coe v10
                                            then case coe v11 of
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                     -> let v13
                                                              = coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du_satisfied_120
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.Spec.Surface.Generators.C_id_10)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Spec.Surface.Generators.C_terminal_18)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Spec.Surface.Generators.C_apply_30)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Spec.Surface.Generators.C_curry_32)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Spec.Surface.Generators.C_In_34)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Spec.Surface.Generators.C_Out_38)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Spec.Surface.Generators.C_ana_40)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Spec.Surface.Generators.C_unit_42)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Spec.Surface.Generators.C_toFloat_44)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
                                                                  (coe v12) in
                                                        coe
                                                          (coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            else (let v12
                                                        = seq
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                               (coe v10)
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                  coe
                                                    (case coe v12 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                         -> if coe v13
                                                              then case coe v14 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                       -> coe
                                                                            seq (coe v15)
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24)
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              else (let v15
                                                                          = seq
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                                                                    coe
                                                                      (case coe v15 of
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                           -> coe
                                                                                MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                           -> coe
                                                                                seq (coe v8)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_16
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_12 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v8))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v8)
                               (coe ("this" :: Data.Text.Text))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20)
                              else coe
                                     seq (coe v11)
                                     (let v12 = d_lookupImportAlias_94 (coe v2) (coe v8) in
                                      coe
                                        (coe
                                           seq (coe v12)
                                           (coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_32
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_32
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_44
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_44
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'unit_46 -> coe v4
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_52
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_52
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_60
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_60
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-reflect
d_cls'45'reflect_582 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_6
d_cls'45'reflect_582 ~v0 ~v1 ~v2 v3 ~v4 = du_cls'45'reflect_582 v3
du_cls'45'reflect_582 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_6
du_cls'45'reflect_582 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_10 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_12 v1 v2
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_14 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_20
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'gen_24
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_22 v1 v2 v3
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_32
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_26 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_44
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_28
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'unit_46
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_34 v1 v2
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_52
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_36 v1 v2 v3
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_60
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.canonDecl
d_canonDecl_674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52
d_canonDecl_674 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 (coe v3)
             (coe
                d_canonExpr_228 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe v0) (coe v1) (coe v4))
      _ -> coe v2
-- Once.Parser.Module.Resolve.sigsOf
d_sigsOf_690 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigsOf_690 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_54 v4 v5
               -> coe d_sigsOf_690 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 v4 v5
               -> coe d_sigsOf_690 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_58 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Name.d_showCanonical_4
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v5))
                    (coe d_sigsOf_690 (coe v0) (coe v3))
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_60 v4 v5 v6
               -> coe d_sigsOf_690 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 v4
               -> coe d_sigsOf_690 (coe v0) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.importedAt
d_importedAt_718 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_64 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_importedAt_718 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_70 v3
               -> coe d_sigsOf_690 (coe v0) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.importedOf
d_importedOf_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_importedOf_726 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_54 v4 v5
               -> coe d_importedOf_726 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 v4 v5
               -> coe d_importedOf_726 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_58 v4 v5
               -> coe d_importedOf_726 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_60 v4 v5 v6
               -> coe d_importedOf_726 (coe v0) (coe v3)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 v4
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_importedAt_718
                       (coe
                          d_expandPath_196
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_46 (coe v4)))
                       (coe
                          d_lookupModule_44 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_46 (coe v4))))
                    (coe d_importedOf_726 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls
d_resolveDecls_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls_752 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> let v6
                 = d_resolveDecls'45'cons'45'aux_786
                     (coe v0) (coe v1) (coe v4)
                     (coe d_resolveDecls_752 (coe v0) (coe v1) (coe v2) (coe v5)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 v7
                  -> coe
                       du_resolveDecls'45'import'45'aux_768 (coe v7)
                       (coe
                          d_lookupModule_44 (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_46 (coe v7)))
                       (coe d_resolveDecls_752 (coe v0) (coe v1) (coe v2) (coe v5))
                _ -> coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls-import-aux
d_resolveDecls'45'import'45'aux_768 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Import_40 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'import'45'aux_768 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
                                    ~v8
  = du_resolveDecls'45'import'45'aux_768 v3 v5 v7
du_resolveDecls'45'import'45'aux_768 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Import_40 ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_64 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_resolveDecls'45'import'45'aux_768 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             seq (coe v3)
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_62 (coe v0))
                          (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Internal error: import path not in ModuleMap: "
                 ::
                 Data.Text.Text)
                (d_showPath_74
                   (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_46 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.consDecl
d_consDecl_770 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consDecl_770 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 v3 v4
           -> coe
                d_consDecl'45'at_776 (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.ResolvedRefs.d_goodRefs'63'_104 (coe v4))
                (coe v1)
         _ -> coe v2)
-- Once.Parser.Module.Resolve.consDecl-at
d_consDecl'45'at_776 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consDecl'45'at_776 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_56 (coe v0)
                             (coe v1))
                          (coe v3)))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("`" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                             ("` refers to `main`, which no definition can refer to"
                              ::
                              Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls-cons-aux
d_resolveDecls'45'cons'45'aux_786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_52 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'cons'45'aux_786 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             d_consDecl_770 (coe d_canonDecl_674 (coe v0) (coe v1) (coe v2))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveImports
d_resolveImports_884 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_64 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveImports_884 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_70 v2
        -> let v3
                 = d_resolveDecls_752
                     (coe d_collectUnaliased_134 (coe v0) (coe v2))
                     (coe d_collectAliases_84 (coe v2)) (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_resolved_18
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_70 (coe v4))
                          (coe d_importedOf_726 (coe v0) (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
