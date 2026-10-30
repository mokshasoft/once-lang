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

module MAlonzo.Code.Once.Extract.Root where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Extract.Names
import qualified MAlonzo.Code.Once.Format
import qualified MAlonzo.Code.Once.Inspect
import qualified MAlonzo.Code.Once.Measure
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Warnings

-- Once.Extract.Root.Runs
d_Runs_6 = ()
data T_Runs_6
  = C_constructor_64 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
                      [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14])
                     (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6])
                     (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                      Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     (MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 -> Bool)
                     ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122)
                     (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6])
                     (Bool ->
                      MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
                      MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (Bool ->
                      MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (Bool ->
                      MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Once.Extract.Root.Runs.parse-source
d_parse'45'source_36 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parse'45'source_36 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.module-imports
d_module'45'imports_38 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_module'45'imports_38 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.import-path
d_import'45'path_40 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_import'45'path_40 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.import-alias
d_import'45'alias_42 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_import'45'alias_42 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.module-has-main
d_module'45'has'45'main_44 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 -> Bool
d_module'45'has'45'main_44 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.resolve-imports
d_resolve'45'imports_46 ::
  T_Runs_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolve'45'imports_46 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.resolved-module
d_resolved'45'module_48 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122
d_resolved'45'module_48 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.warnings
d_warnings_50 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_warnings_50 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.assembly
d_assembly_52 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_assembly_52 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.signatures
d_signatures_54 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_signatures_54 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.check
d_check_56 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_check_56 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.dump-ir
d_dump'45'ir_58 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dump'45'ir_58 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.stats
d_stats_60 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stats_60 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.format
d_format_62 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_format_62 v0
  = case coe v0 of
      C_constructor_64 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.runs
d_runs_66 :: T_Runs_6
d_runs_66
  = coe
      C_constructor_64
      (coe MAlonzo.Code.Once.Compile.d_parseSourceToModule_624)
      (coe MAlonzo.Code.Once.Extract.Names.d_module'45'imports_34)
      (coe MAlonzo.Code.Once.Extract.Names.d_import'45'path_50)
      (coe MAlonzo.Code.Once.Extract.Names.d_import'45'alias_54)
      (coe MAlonzo.Code.Once.Extract.Names.d_module'45'has'45'main_6)
      (coe MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveImports_904)
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.Parser.Module.Core.d_rmodule_14 (coe v0)))
      (coe MAlonzo.Code.Once.Warnings.d_warningsFor_378)
      (coe MAlonzo.Code.Once.Compile.d_assemblyFromModule_1562)
      (coe MAlonzo.Code.Once.Inspect.d_signatures_40)
      (coe MAlonzo.Code.Once.Inspect.d_check_48)
      (coe MAlonzo.Code.Once.Inspect.d_dumpIR_68)
      (coe MAlonzo.Code.Once.Measure.d_statsOf_4)
      (coe MAlonzo.Code.Once.Format.d_formatSource_14)
