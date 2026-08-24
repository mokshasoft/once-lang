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

module MAlonzo.Code.Once.Adequacy.ResolverLits where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.ResolverLits.canonVar-lits
d_canonVar'45'lits_12 ::
  Bool ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonVar'45'lits_12 = erased
-- Once.Adequacy.ResolverLits.negLits-canonVar
d_negLits'45'canonVar_26 ::
  Bool ->
  Maybe [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negLits'45'canonVar_26 = erased
-- Once.Adequacy.ResolverLits.canonExpr-lits
d_canonExpr'45'lits_42 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonExpr'45'lits_42 = erased
-- Once.Adequacy.ResolverLits.negLits-lits
d_negLits'45'lits_52 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negLits'45'lits_52 = erased
-- Once.Adequacy.ResolverLits.canonDecl-lits
d_canonDecl'45'lits_402 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_canonDecl'45'lits_402 = erased
-- Once.Adequacy.ResolverLits.declsIntLits
d_declsIntLits_436 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] -> [Integer]
d_declsIntLits_436 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_declIntLits_46 (coe v1))
             (coe d_declsIntLits_436 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolverLits.sigsWithOwner-lits
d_sigsWithOwner'45'lits_446 ::
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigsWithOwner'45'lits_446 = erased
-- Once.Adequacy.ResolverLits.declsIntLits-++
d_declsIntLits'45''43''43'_474 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_declsIntLits'45''43''43'_474 = erased
-- Once.Adequacy.ResolverLits.inj₂-inj
d_inj'8322''45'inj_494 ::
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_494 = erased
-- Once.Adequacy.ResolverLits.inj₁≢inj₂
d_inj'8321''8802'inj'8322'_504 ::
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_inj'8321''8802'inj'8322'_504 = erased
-- Once.Adequacy.ResolverLits.resolveDecls-lits
d_resolveDecls'45'lits_518 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveDecls'45'lits_518 = erased
-- Once.Adequacy.ResolverLits.moduleIntLits≡decls
d_moduleIntLits'8801'decls_916 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_moduleIntLits'8801'decls_916 = erased
-- Once.Adequacy.ResolverLits.resolver-preserves-intLits
d_resolver'45'preserves'45'intLits_930 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolver'45'preserves'45'intLits_930 = erased
