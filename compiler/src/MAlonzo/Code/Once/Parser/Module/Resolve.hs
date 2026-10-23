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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Internal.ResolvedRefs
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_20
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
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectAliases_84 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_collectAliases_84 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_18 v4
                  -> case coe v4 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v5 v6
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
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sigNames_126 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_sigNames_126 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_14 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_sigNames_126 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.collectUnaliased
d_collectUnaliased_134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectUnaliased_134 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_collectUnaliased_134 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_18 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v8 = d_lookupModule_44 (coe v0) (coe v6) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26 v10
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
-- Once.Parser.Module.Resolve.isBuiltinName
d_isBuiltinName_196 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isBuiltinName_196 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_22 (coe v0))
-- Once.Parser.Module.Resolve.isBuiltinName-sound
d_isBuiltinName'45'sound_202 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_isBuiltinName'45'sound_202 v0 ~v1
  = du_isBuiltinName'45'sound_202 v0
du_isBuiltinName'45'sound_202 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_isBuiltinName'45'sound_202 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
         (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_fromSum_132)
         (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_toSum_126)
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
               erased
               (\ v1 ->
                  coe
                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                    (coe v0))
               (coe
                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                  (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
                  (coe
                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                     ("id" :: Data.Text.Text))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
               (coe
                  (\ v1 ->
                     coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                       erased
                       (\ v2 ->
                          coe
                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                            (coe v0))
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                          (coe v1))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe ("fst" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe ("snd" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe ("inl" :: Data.Text.Text))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("inr" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe ("unit" :: Data.Text.Text))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe ("pair" :: Data.Text.Text))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe ("terminal" :: Data.Text.Text))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe ("initial" :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe ("curry" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe ("apply" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe ("compose" :: Data.Text.Text))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe ("case" :: Data.Text.Text))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("cata" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("ana" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe ("In" :: Data.Text.Text))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe ("Out" :: Data.Text.Text))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
-- Once.Parser.Module.Resolve.isBuiltinName-false
d_isBuiltinName'45'false_210 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isBuiltinName'45'false_210 = erased
-- Once.Parser.Module.Resolve.¬GenWord-isBuiltinName
d_'172'GenWord'45'isBuiltinName_220 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'GenWord'45'isBuiltinName_220 = erased
-- Once.Parser.Module.Resolve.expandPath
d_expandPath_240 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_expandPath_240 v0
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
d_canonVar_258 ::
  Bool ->
  Bool ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_canonVar_258 v0 v1 v2 v3
  = if coe v0
      then coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 (coe v3)
      else (if coe v1
              then coe
                     MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                     (coe
                        MAlonzo.Code.Once.Spec.Name.C_canonical_12
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("Generators" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
              else (case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                        -> coe
                             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                             (coe
                                MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe d_expandPath_240 (coe v4))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> coe
                             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                             (coe
                                MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Parser.Module.Resolve.canonExpr
d_canonExpr_270 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_canonExpr_270 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v4
        -> coe
             d_canonVar_258
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
                   (coe
                      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                   (coe v4) (coe v0)))
             (coe d_isBuiltinName_196 (coe v4))
             (coe d_lookupUnaliased_166 (coe v1) (coe v4)) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v4 v5
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
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
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
                                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
                                           (coe
                                              MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                 (coe d_expandPath_240 (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74
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
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v4 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 (coe v4)
             (coe
                d_canonExpr_270
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 (coe v4)
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe
                d_canonExpr_270
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
             (coe
                d_canonExpr_270
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v0))
                (coe v1) (coe v2) (coe v6))
             (coe v7)
             (coe
                d_canonExpr_270
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v0))
                (coe v1) (coe v2) (coe v8))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v4 -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v4 v5 v6
        -> coe v3
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 (coe v4)
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v4
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96
             (coe d_canonExpr_270 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-canon
d_cls'45'canon_470 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14
d_cls'45'canon_470 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'var_18
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v6
               -> let v7
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                               (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v6))
                               (coe v0)) in
                  coe
                    (let v8
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_fromSum_132)
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_toSum_126)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                        erased
                                        (\ v8 ->
                                           coe
                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                             (coe v6))
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                           (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              v6)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              ("id" :: Data.Text.Text))))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                                        (coe
                                           (\ v8 ->
                                              coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v9 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v6))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v6) (coe v8))))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("fst" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe ("snd" :: Data.Text.Text))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe ("inl" :: Data.Text.Text))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe ("inr" :: Data.Text.Text))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe ("unit" :: Data.Text.Text))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe ("pair" :: Data.Text.Text))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe ("terminal" :: Data.Text.Text))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe ("initial" :: Data.Text.Text))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe ("curry" :: Data.Text.Text))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         ("apply"
                                                                          ::
                                                                          Data.Text.Text))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            ("compose"
                                                                             ::
                                                                             Data.Text.Text))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                            (coe
                                                                               ("case"
                                                                                ::
                                                                                Data.Text.Text))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                               (coe
                                                                                  ("cata"
                                                                                   ::
                                                                                   Data.Text.Text))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                  (coe
                                                                                     ("ana"
                                                                                      ::
                                                                                      Data.Text.Text))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                     (coe
                                                                                        ("In"
                                                                                         ::
                                                                                         Data.Text.Text))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                        (coe
                                                                                           ("Out"
                                                                                            ::
                                                                                            Data.Text.Text))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))) in
                     coe
                       (let v9 = d_lookupUnaliased_166 (coe v1) (coe v6) in
                        coe
                          (if coe v7
                             then coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'var_18
                             else (if coe v8
                                     then coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28
                                     else coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'qual_24
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v7 v8
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
                                     (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28)
                              else coe
                                     seq (coe v11)
                                     (let v12 = d_lookupImportAlias_94 (coe v2) (coe v8) in
                                      coe
                                        (coe
                                           seq (coe v12)
                                           (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'let_36
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'let_36
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'destr_48
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'destr_48
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'unit_50 -> coe v4
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'annot_56
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'annot_56
      MAlonzo.Code.Once.Internal.Syntax.C_cls'45'binop_64
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'binop_64
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-reflect
d_cls'45'reflect_608 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14
d_cls'45'reflect_608 ~v0 ~v1 ~v2 v3 ~v4 = du_cls'45'reflect_608 v3
du_cls'45'reflect_608 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14
du_cls'45'reflect_608 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v1
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'var_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v1 v2
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'qual_24
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v1
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v1 v2 v3
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'let_36
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'destr_48
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'unit_50
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v1 v2
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'annot_56
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v1 v2 v3
        -> coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'binop_64
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.canonDecl
d_canonDecl_694 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8
d_canonDecl_694 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_12 v3 v4
        -> coe
             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_12 (coe v3)
             (coe
                d_canonExpr_270 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe v0) (coe v1) (coe v4))
      _ -> coe v2
-- Once.Parser.Module.Resolve.signaturesWithOwner
d_signaturesWithOwner_710 ::
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8]
d_signaturesWithOwner_710 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_signaturesWithOwner_710 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_14 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_14 (coe v5)
                          (coe v0) (coe v7))
                       (coe d_signaturesWithOwner_710 (coe v0) (coe v3))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.ownerOf
d_ownerOf_724 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Import_98 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ownerOf_724 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkImport_108 v1 v2
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe d_expandPath_240 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls
d_resolveDecls_730 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls_730 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> let v6
                 = d_resolveDecls'45'cons'45'aux_764
                     (coe v0) (coe v1) (coe v4)
                     (coe d_resolveDecls_730 (coe v0) (coe v1) (coe v2) (coe v5)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_18 v7
                  -> coe
                       du_resolveDecls'45'import'45'aux_746 (coe v7)
                       (coe
                          d_lookupModule_44 (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_104 (coe v7)))
                       (coe d_resolveDecls_730 (coe v0) (coe v1) (coe v2) (coe v5))
                _ -> coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls-import-aux
d_resolveDecls'45'import'45'aux_746 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Import_98 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'import'45'aux_746 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7
                                    ~v8
  = du_resolveDecls'45'import'45'aux_746 v3 v5 v7
du_resolveDecls'45'import'45'aux_746 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Import_98 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_resolveDecls'45'import'45'aux_746 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.Parser.Module.Core.C_DImport_18 (coe v0))
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe
                                    d_signaturesWithOwner_710 (coe d_ownerOf_724 (coe v0)) (coe v4))
                                 (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Internal error: import path not in ModuleMap: "
                 ::
                 Data.Text.Text)
                (d_showPath_74
                   (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_104 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.consDecl
d_consDecl_748 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consDecl_748 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_12 v3 v4
           -> coe
                d_consDecl'45'at_754 (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.ResolvedRefs.d_goodRefs'63'_106
                   (coe v4))
                (coe v1)
         _ -> coe v2)
-- Once.Parser.Module.Resolve.consDecl-at
d_consDecl'45'at_754 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consDecl'45'at_754 v0 v1 v2 v3
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
                             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_12 (coe v0)
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
d_resolveDecls'45'cons'45'aux_764 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'cons'45'aux_764 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             d_consDecl_748 (coe d_canonDecl_694 (coe v0) (coe v1) (coe v2))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveImports
d_resolveImports_862 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveImports_862 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26 v2
        -> let v3
                 = d_resolveDecls_730
                     (coe d_collectUnaliased_134 (coe v0) (coe v2))
                     (coe d_collectAliases_84 (coe v2)) (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26 (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
