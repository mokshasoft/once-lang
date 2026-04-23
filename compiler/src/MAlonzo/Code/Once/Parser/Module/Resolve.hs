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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Parser.Module.Core
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
-- Once.Parser.Module.Resolve.signaturesWithOwner
d_signaturesWithOwner_70 ::
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
d_signaturesWithOwner_70 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4 = d_signaturesWithOwner_70 (coe v0) (coe v3) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 (coe v5)
                          (coe v0) (coe v7))
                       (coe d_signaturesWithOwner_70 (coe v0) (coe v3))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveDecls
d_resolveDecls_84 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveDecls_84 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
      (:) v2 v3
        -> let v4
                 = let v4 = d_resolveDecls_84 (coe v0) (coe v3) in
                   coe
                     (case coe v4 of
                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                          -> coe
                               MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v5))
                        _ -> MAlonzo.RTE.mazUnreachableError) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v5
                  -> let v6
                           = d_lookupModule_40
                               (coe v0)
                               (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v5)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v8
                                   -> let v9 = d_resolveDecls_84 (coe v0) (coe v3) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> coe v9
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                             -> coe
                                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                     (coe
                                                        d_signaturesWithOwner_70
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Module.Core.d_alias_28
                                                           (coe v5))
                                                        (coe v8))
                                                     (coe v10))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("Internal error: import path not in ModuleMap: "
                                     ::
                                     Data.Text.Text)
                                    (coe
                                       du_showPath_106
                                       (coe
                                          MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v5))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve._.showPath
d_showPath_106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPath_106 ~v0 ~v1 ~v2 v3 = du_showPath_106 v3
du_showPath_106 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showPath_106 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("." :: Data.Text.Text) (coe du_showPath_106 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe v1
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Resolve.resolveImports
d_resolveImports_172 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveImports_172 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> let v3 = d_resolveDecls_84 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
