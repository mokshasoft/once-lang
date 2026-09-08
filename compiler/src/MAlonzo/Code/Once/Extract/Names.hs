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

module MAlonzo.Code.Once.Extract.Names where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Extract.Names.module-has-main
d_module'45'has'45'main_6 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> Bool
d_module'45'has'45'main_6 v0
  = coe
      du_go_26
      (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
-- Once.Extract.Names._.is-main
d_is'45'main_14 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_is'45'main_14 ~v0 v1 = du_is'45'main_14 v1
du_is'45'main_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
du_is'45'main_14 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe v2)
                else coe seq (coe v3) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Extract.Names._.go
d_go_26 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] -> Bool
d_go_26 ~v0 v1 = du_go_26 v1
du_go_26 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] -> Bool
du_go_26 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_go_26 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 v4 v5
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe du_is'45'main_14 (coe v4)) (coe du_go_26 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Names.module-imports
d_module'45'imports_34 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_module'45'imports_34 v0
  = coe
      du_go_42
      (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
-- Once.Extract.Names._.go
d_go_42 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_42 ~v0 v1 = du_go_42 v1
du_go_42 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_42 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_42 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_14 (coe v4))
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_alias_16 (coe v4)))
                       (coe du_go_42 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Names.import-path
d_import'45'path_50 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_import'45'path_50 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Names.import-alias
d_import'45'alias_54 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_import'45'alias_54 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
