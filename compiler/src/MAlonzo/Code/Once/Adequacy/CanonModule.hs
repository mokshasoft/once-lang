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

module MAlonzo.Code.Once.Adequacy.CanonModule where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Adequacy.CanonModuleTyped
import qualified MAlonzo.Code.Once.Adequacy.CanonResolve
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CanonModule.has-valid-main-canon
d_has'45'valid'45'main'45'canon_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CanonModule.has-valid-main-canon"
-- Once.Adequacy.CanonModule.resolver-preserves-typing-imports
d_resolver'45'preserves'45'typing'45'imports_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CanonModule.resolver-preserves-typing-imports"
-- Once.Adequacy.CanonModule.canon-preserves-typing
d_canon'45'preserves'45'typing_34 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_canon'45'preserves'45'typing_34 v0 v1 v2 v3
  = coe
      d_go_56 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
         (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v1)))
-- Once.Adequacy.CanonModule._.ds
d_ds_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
d_ds_48 ~v0 v1 ~v2 ~v3 = du_ds_48 v1
du_ds_48 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
du_ds_48 v0
  = coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)
-- Once.Adequacy.CanonModule._.go
d_go_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_56 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Adequacy.CanonModuleTyped.d_canonModule_6
                          (coe du_ds_48 (coe v1)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.Adequacy.CanonModuleTyped.d_module'45'typed'45'canon_302
                                (coe du_ds_48 (coe v1)) (coe v2))
                             (coe
                                d_has'45'valid'45'main'45'canon_10 (coe du_ds_48 (coe v1)) v2
                                v3))))
             else coe
                    seq (coe v6)
                    (coe d_resolver'45'preserves'45'typing'45'imports_22 v0 v1 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonModule._._.res-eq
d_res'45'eq_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'eq_64 = erased
