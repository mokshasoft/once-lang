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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Inspect
import qualified MAlonzo.Code.Once.Measure
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Warnings

-- Once.Extract.Root.Runs
d_Runs_6 = ()
data T_Runs_6
  = C_constructor_60 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                     (MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
                      [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14])
                     (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6])
                     (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                      Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     (MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
                      Maybe MAlonzo.Code.Once.IR.T_IR_16)
                     ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                      MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
                      MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
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
d_parse'45'source_34 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parse'45'source_34 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.module-imports
d_module'45'imports_36 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_module'45'imports_36 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.import-path
d_import'45'path_38 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_import'45'path_38 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.import-alias
d_import'45'alias_40 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_import'45'alias_40 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.main-ir
d_main'45'ir_42 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_main'45'ir_42 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.resolve-imports
d_resolve'45'imports_44 ::
  T_Runs_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolve'45'imports_44 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.warnings
d_warnings_46 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_warnings_46 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.assembly
d_assembly_48 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_assembly_48 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.signatures
d_signatures_50 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_signatures_50 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.check
d_check_52 ::
  T_Runs_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_check_52 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.dump-ir
d_dump'45'ir_54 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dump'45'ir_54 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.stats
d_stats_56 ::
  T_Runs_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_stats_56 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.Runs.format
d_format_58 ::
  T_Runs_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_format_58 v0
  = case coe v0 of
      C_constructor_60 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Root.runs
d_runs_62 :: T_Runs_6
d_runs_62
  = coe
      C_constructor_60 (coe MAlonzo.Code.Once.Parser.d_parseStrict_74)
      (coe MAlonzo.Code.Once.Extract.Names.d_module'45'imports_20)
      (coe MAlonzo.Code.Once.Extract.Names.d_import'45'path_24)
      (coe MAlonzo.Code.Once.Extract.Names.d_import'45'alias_28)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1260)
      (coe MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveImports_904)
      (coe MAlonzo.Code.Once.Warnings.d_warningsFor_378)
      (coe MAlonzo.Code.Once.Compile.d_assemblyFromModule_1584)
      (coe MAlonzo.Code.Once.Inspect.d_signatures_40)
      (coe MAlonzo.Code.Once.Inspect.d_check_48)
      (coe MAlonzo.Code.Once.Inspect.d_dumpIR_68)
      (coe MAlonzo.Code.Once.Measure.d_statsOf_4)
      (coe MAlonzo.Code.Once.Format.d_formatSource_14)
