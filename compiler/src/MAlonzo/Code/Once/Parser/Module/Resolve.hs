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
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Principal
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Module.Resolve.ModuleMap
d_ModuleMap_8 :: ()
d_ModuleMap_8 = erased
-- Once.Parser.Module.Resolve._path≟_
d__path'8799'__10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d__path'8799'__10 v0 v1
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
                              then coe seq (coe v8) (coe d__path'8799'__10 (coe v3) (coe v5))
                              else coe seq (coe v8) (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupModule
d_lookupModule_40 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_lookupModule_40 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d__path'8799'__10 (coe v4) (coe v1) in
                  coe
                    (if coe v6
                       then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       else coe d_lookupModule_40 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.showPath
d_showPath_70 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPath_70 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("." :: Data.Text.Text) (d_showPath_70 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.AliasMap
d_AliasMap_78 :: ()
d_AliasMap_78 = erased
-- Once.Parser.Module.Resolve.collectAliases
d_collectAliases_80 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectAliases_80 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_collectAliases_80 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v4
                  -> case coe v4 of
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v5))
                                     (coe d_collectAliases_80 (coe v2))
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupImportAlias
d_lookupImportAlias_90 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lookupImportAlias_90 v0 v1
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
                                     seq (coe v8) (coe d_lookupImportAlias_90 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.UnaliasedMap
d_UnaliasedMap_120 :: ()
d_UnaliasedMap_120 = erased
-- Once.Parser.Module.Resolve.sigNames
d_sigNames_122 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sigNames_122 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_sigNames_122 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_sigNames_122 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.collectUnaliased
d_collectUnaliased_130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectUnaliased_130 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_collectUnaliased_130 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v5
                  -> case coe v5 of
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v8 = d_lookupModule_40 (coe v0) (coe v6) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v10
                                                 -> coe
                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du_map_22
                                                         (coe
                                                            (\ v11 ->
                                                               coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v11) (coe v6)))
                                                         (coe d_sigNames_122 (coe v10)))
                                                      (coe d_collectUnaliased_130 (coe v0) (coe v3))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe d_collectUnaliased_130 (coe v0) (coe v3)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.lookupUnaliased
d_lookupUnaliased_162 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lookupUnaliased_162 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupUnaliased_162 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.isBuiltinName
d_isBuiltinName_192 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isBuiltinName_192 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_48 (coe v0))
-- Once.Parser.Module.Resolve.isBuiltinName-sound
d_isBuiltinName'45'sound_198 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_isBuiltinName'45'sound_198 v0 ~v1
  = du_isBuiltinName'45'sound_198 v0
du_isBuiltinName'45'sound_198 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_isBuiltinName'45'sound_198 v0
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
d_isBuiltinName'45'false_206 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isBuiltinName'45'false_206 = erased
-- Once.Parser.Module.Resolve.¬GenWord-isBuiltinName
d_'172'GenWord'45'isBuiltinName_216 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'GenWord'45'isBuiltinName_216 = erased
-- Once.Parser.Module.Resolve.elemStr
d_elemStr_236 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_elemStr_236 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
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
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v5)
                       else coe seq (coe v6) (coe d_elemStr_236 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.pdn-go
d_pdn'45'go_260 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_pdn'45'go_260 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> let v4 = d_pdn'45'go_260 (coe v3) (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v5 v6
                  -> let v7 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v6) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                            -> let v9
                                     = MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                         (coe
                                            MAlonzo.Code.Once.Type.d_extractGround_316 (coe v6)
                                            (coe v8)) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           d_pdn'45'go_260 (coe v3)
                                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                           (coe
                                              d_pdn'45'go_260 (coe v3)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                 (coe v5)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                 (coe
                                    d_pdn'45'go_260 (coe v3)
                                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v5 v6 v7
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> coe
                              d_pdn'45'go_260 (coe v3)
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v8
                                  = MAlonzo.Code.Once.TypeCheck.Principal.d_pgSchema_2132
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Principal.d_finishP_2110
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Principal.d_pInfer_1372
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Principal.d_projSchemas_932
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370)))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                            (coe v7) (coe (0 :: Integer))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                        (coe d_pdn'45'go_260 (coe v3) (coe v1))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe d_pdn'45'go_260 (coe v3) (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v5 v6 v7 v8
                  -> coe
                       d_pdn'45'go_260 (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.polyDefNames
d_polyDefNames_356 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_polyDefNames_356 v0
  = coe
      d_pdn'45'go_260 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.Parser.Module.Resolve.expandPath
d_expandPath_360 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_expandPath_360 v0
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
d_canonVar_378 ::
  Bool ->
  Bool ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_canonVar_378 v0 v1 v2 v3
  = if coe v0
      then coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v3)
      else (if coe v1
              then coe
                     MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                     (coe
                        MAlonzo.Code.Once.CanonicalName.C_canonical_10
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("Generators" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
              else (case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                        -> coe
                             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                             (coe
                                MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe d_expandPath_360 (coe v4))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> coe
                             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                             (coe
                                MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Parser.Module.Resolve.canonExpr
d_canonExpr_390 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_canonExpr_390 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
        -> coe
             d_canonVar_378 (coe d_elemStr_236 (coe v4) (coe v0))
             (coe d_isBuiltinName_192 (coe v4))
             (coe d_lookupUnaliased_162 (coe v1) (coe v4)) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v4 v5
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
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                 (coe
                                    MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                       else coe
                              seq (coe v8)
                              (let v9 = d_lookupImportAlias_90 (coe v2) (coe v5) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe
                                           MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                           (coe
                                              MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                 (coe d_expandPath_360 (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4 -> coe v3
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 (coe v4)
             (coe
                d_canonExpr_390
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 (coe v4)
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe
                d_canonExpr_390
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
             (coe
                d_canonExpr_390
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v0))
                (coe v1) (coe v2) (coe v6))
             (coe v7)
             (coe
                d_canonExpr_390
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v0))
                (coe v1) (coe v2) (coe v8))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52 -> coe v3
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4 -> coe v3
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v4 v5 v6 v7 -> coe v3
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v4 -> coe v3
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v4)) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 (coe v4)
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64
             (d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 (coe v4)
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-canon
d_cls'45'canon_612 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100
d_cls'45'canon_612 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_104
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
               -> let v7 = d_elemStr_236 (coe v6) (coe v0) in
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
                       (let v9 = d_lookupUnaliased_162 (coe v1) (coe v6) in
                        coe
                          (if coe v7
                             then coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_104
                             else (if coe v8
                                     then coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
                                     else coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_110
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v7 v8
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
                                     (coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114)
                              else coe
                                     seq (coe v11)
                                     (let v12 = d_lookupImportAlias_90 (coe v2) (coe v8) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_110
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_122
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_122
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_134
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_134
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'unit_136 -> coe v4
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'str_140
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'str_140
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_146
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_146
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_154
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_154
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.cls-reflect
d_cls'45'reflect_756 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100
d_cls'45'reflect_756 ~v0 ~v1 ~v2 v3 ~v4 = du_cls'45'reflect_756 v3
du_cls'45'reflect_756 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100
du_cls'45'reflect_756 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_104
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_110
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_122
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_134
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'unit_136
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v1
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'str_140
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v1 v2
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_146
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v1 v2 v3
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_154
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.canonDecl
d_canonDecl_854 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32
d_canonDecl_854 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 (coe v4) (coe v5)
             (coe d_canonExpr_390 (coe v0) (coe v1) (coe v2) (coe v6))
      _ -> coe v3
-- Once.Parser.Module.Resolve.signaturesWithOwner
d_signaturesWithOwner_876 ::
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
d_signaturesWithOwner_876 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_signaturesWithOwner_876 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 (coe v5)
                          (coe v0) (coe v7) (coe v8))
                       (coe d_signaturesWithOwner_876 (coe v0) (coe v3))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.ownerOf
d_ownerOf_892 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ownerOf_892 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30 v1 v2
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe d_showPath_70 (coe d_expandPath_360 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls
d_resolveDecls_898 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls_898 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      (:) v5 v6
        -> let v7
                 = d_resolveDecls'45'cons'45'aux_928
                     (coe v0) (coe v1) (coe v2) (coe v5)
                     (coe
                        d_resolveDecls_898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v8
                  -> coe
                       du_resolveDecls'45'import'45'aux_916 (coe v8)
                       (coe
                          d_lookupModule_40 (coe v3)
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v8)))
                       (coe
                          d_resolveDecls_898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
                _ -> coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls-import-aux
d_resolveDecls'45'import'45'aux_916 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'import'45'aux_916 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
                                    v8 ~v9
  = du_resolveDecls'45'import'45'aux_916 v4 v6 v8
du_resolveDecls'45'import'45'aux_916 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_resolveDecls'45'import'45'aux_916 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 d_signaturesWithOwner_876 (coe d_ownerOf_892 (coe v0)) (coe v4))
                              (coe v5))
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
                (d_showPath_70
                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls-cons-aux
d_resolveDecls'45'cons'45'aux_928 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls'45'cons'45'aux_928 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_canonDecl_854 (coe v0) (coe v1) (coe v2) (coe v3)) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveImports
d_resolveImports_1018 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveImports_1018 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> let v3
                 = d_resolveDecls_898
                     (coe d_polyDefNames_356 (coe v2))
                     (coe d_collectUnaliased_130 (coe v0) (coe v2))
                     (coe d_collectAliases_80 (coe v2)) (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
