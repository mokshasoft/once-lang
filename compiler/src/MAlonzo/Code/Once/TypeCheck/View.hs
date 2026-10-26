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

module MAlonzo.Code.Once.TypeCheck.View where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.TypeCheck.Scope

-- Once.TypeCheck.View.Declared
d_Declared_16 a0 a1 a2 a3 a4 = ()
data T_Declared_16
  = C_declared_34 AgdaAny
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   AgdaAny ->
                   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
-- Once.TypeCheck.View.Declared.honest
d_honest_28 :: T_Declared_16 -> AgdaAny
d_honest_28 v0
  = case coe v0 of
      C_declared_34 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.Declared.member
d_member_32 ::
  T_Declared_16 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_32 v0
  = case coe v0 of
      C_declared_34 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.ImportAt
d_ImportAt_40 a0 a1 a2 a3 a4 = ()
newtype T_ImportAt_40
  = C_def_54 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Once.TypeCheck.View.ImportAt.entryOf
d_entryOf_50 ::
  T_ImportAt_40 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_50 v0
  = case coe v0 of
      C_def_54 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.ImportAt.mono
d_mono_52 ::
  T_ImportAt_40 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono_52 = erased
-- Once.TypeCheck.View.View
d_View_62 a0 a1 a2 a3 a4 a5 = ()
data T_View_62
  = C_constructor_138 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_40)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_16)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
                       MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Fin.Base.T_Fin_10)
-- Once.TypeCheck.View.View.imported
d_imported_108 ::
  T_View_62 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_40
d_imported_108 v0
  = case coe v0 of
      C_constructor_138 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.View.declares
d_declares_114 ::
  T_View_62 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_16
d_declares_114 v0
  = case coe v0 of
      C_constructor_138 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.View.entry
d_entry_124 ::
  T_View_62 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_124 v0
  = case coe v0 of
      C_constructor_138 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.View.View.entryIs
d_entryIs_136 ::
  T_View_62 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entryIs_136 = erased
-- Once.TypeCheck.View.Views
d_Views_142 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer -> MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 -> ()
d_Views_142 = erased
-- Once.TypeCheck.View.InView
d_InView_156 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InView_156
  = C_iv'45'imp_174 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_iv'45'poly_186 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                     MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                     [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
