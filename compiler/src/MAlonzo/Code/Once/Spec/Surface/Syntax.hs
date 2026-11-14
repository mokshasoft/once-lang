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
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Surface.Syntax.PolyFunctor
d_PolyFunctor_8 = ()
data T_PolyFunctor_8
  = C_PK_12 T_PolyType_10 | C_PId_14 |
    C__P'8853'__16 T_PolyFunctor_8 T_PolyFunctor_8 |
    C__P'8855'__18 T_PolyFunctor_8 T_PolyFunctor_8
-- Once.Spec.Surface.Syntax.PolyType
d_PolyType_10 = ()
data T_PolyType_10
  = C_PUnit_20 | C_PVoid_22 | C_PInt_24 | C_PFloat_26 |
    C__P'42'__28 T_PolyType_10 T_PolyType_10 |
    C__P'43'__30 T_PolyType_10 T_PolyType_10 |
    C__P'8658''91'_'93'__32 T_PolyType_10
                            MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_PolyType_10 |
    C_PAct_34 T_PolyType_10 T_PolyType_10 |
    C_PEff_36 T_PolyType_10 T_PolyType_10 | C_Pμ_38 T_PolyFunctor_8 |
    C_Pν_40 T_PolyFunctor_8 MAlonzo.Code.Once.Spec.Grade.T_Finite_34 |
    C_PTVar_42 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Spec.Surface.Syntax.Expr
d_Expr_44 = ()
data T_Expr_44
  = C_RVar_46 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RQualified_48 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RResolved_50 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_RApp_52 T_Expr_44 T_Expr_44 |
    C_RLam_54 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_44 |
    C_RLet_56 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_44
              T_Expr_44 |
    C_RPair_58 T_Expr_44 T_Expr_44 |
    C_RDestruct_60 T_Expr_44
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_44
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_44 |
    C_RUnit_62 | C_RInt_64 Integer |
    C_RFloat_66 MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 Integer
                Integer Integer |
    C_RAnnot_68 T_Expr_44 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_RBinOp_70 MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36
                T_Expr_44 T_Expr_44 |
    C_RNeg_72 T_Expr_44
-- Once.Spec.Surface.Syntax.signedDecimal
d_signedDecimal_74 ::
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8
d_signedDecimal_74 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Float.Value.C_pos_10
        -> coe
             MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v1)
             (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Float.Value.C_neg_12
        -> coe
             MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
             (coe
                MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v1)
                (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.NegativeZero
d_NegativeZero_88 a0 a1 a2 = ()
data T_NegativeZero_88 = C_neg'45'zero_90
-- Once.Spec.Surface.Syntax.Import
d_Import_92 = ()
data T_Import_92
  = C_mkImport_102 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                   (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Spec.Surface.Syntax.Import.path
d_path_98 ::
  T_Import_92 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_98 v0
  = case coe v0 of
      C_mkImport_102 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Import.alias
d_alias_100 ::
  T_Import_92 -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_alias_100 v0
  = case coe v0 of
      C_mkImport_102 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Decl
d_Decl_104 = ()
data T_Decl_104
  = C_DTypeSig_106 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_PolyType_10 |
    C_DFunDef_108 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  T_Expr_44 |
    C_DSignature_110 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_PolyType_10 |
    C_DTypeAlias_112 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_PolyType_10 |
    C_DImport_114 T_Import_92
-- Once.Spec.Surface.Syntax.Module
d_Module_116 = ()
newtype T_Module_116 = C_mkModule_122 [T_Decl_104]
-- Once.Spec.Surface.Syntax.Module.decls
d_decls_120 :: T_Module_116 -> [T_Decl_104]
d_decls_120 v0
  = case coe v0 of
      C_mkModule_122 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
