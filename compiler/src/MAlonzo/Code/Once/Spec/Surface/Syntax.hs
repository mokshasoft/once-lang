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

module MAlonzo.Code.Once.Spec.Surface.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Generators
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Type
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Surface.Syntax.Expr
d_Expr_8 = ()
data T_Expr_8
  = C_RVar_10 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RQualified_12 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RResolved_14 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_RGen_16 MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 |
    C_RApp_18 T_Expr_8 T_Expr_8 |
    C_RLam_20 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_8 |
    C_RLet_22 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_8
              T_Expr_8 |
    C_RPair_24 T_Expr_8 T_Expr_8 |
    C_RDestruct_26 T_Expr_8 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_Expr_8 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_8 |
    C_RUnit_28 | C_RInt_30 Integer |
    C_RFloat_32 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 Integer
                Integer Integer |
    C_RAnnot_34 T_Expr_8 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_RBinOp_36 MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36
                T_Expr_8 T_Expr_8 |
    C_RNeg_38 T_Expr_8
-- Once.Spec.Surface.Syntax.Import
d_Import_40 = ()
data T_Import_40
  = C_mkImport_50 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Spec.Surface.Syntax.Import.path
d_path_46 ::
  T_Import_40 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_46 v0
  = case coe v0 of
      C_mkImport_50 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Import.alias
d_alias_48 ::
  T_Import_40 -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_alias_48 v0
  = case coe v0 of
      C_mkImport_50 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Decl
d_Decl_52 = ()
data T_Decl_52
  = C_DTypeSig_54 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 |
    C_DFunDef_56 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_8 |
    C_DSignature_58 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 |
    C_DTypeAlias_60 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                    MAlonzo.Code.Once.Spec.Surface.Type.T_PolyType_10 |
    C_DImport_62 T_Import_40
-- Once.Spec.Surface.Syntax.Module
d_Module_64 = ()
newtype T_Module_64 = C_mkModule_70 [T_Decl_52]
-- Once.Spec.Surface.Syntax.Module.decls
d_decls_68 :: T_Module_64 -> [T_Decl_52]
d_decls_68 v0
  = case coe v0 of
      C_mkModule_70 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
