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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax

-- Once.Extract.Names.imports-of
d_imports'45'of_6 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports'45'of_6 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v3 v4
               -> coe d_imports'45'of_6 (coe v2)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v3 v4
               -> coe d_imports'45'of_6 (coe v2)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v3 v4
               -> coe d_imports'45'of_6 (coe v2)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeAlias_118 v3 v4 v5
               -> coe d_imports'45'of_6 (coe v2)
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_DImport_120 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_path_104 (coe v3))
                       (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_alias_106 (coe v3)))
                    (coe d_imports'45'of_6 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Names.module-imports
d_module'45'imports_20 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_module'45'imports_20 v0
  = coe
      d_imports'45'of_6
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.d_decls_126 (coe v0))
-- Once.Extract.Names.import-path
d_import'45'path_24 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_import'45'path_24 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Extract.Names.import-alias
d_import'45'alias_28 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_import'45'alias_28 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
