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
import qualified MAlonzo.Code.Data.Nat.Base
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
  = coe
      MAlonzo.Code.Once.Spec.Float.Decimal.C_'10216'_'10217'_'47'10'94'__22
      (coe v0)
      (coe
         addInt
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v3)))
         (coe v2))
      (coe v3)
-- Once.Spec.Surface.Syntax.Import
d_Import_84 = ()
data T_Import_84
  = C_mkImport_94 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Spec.Surface.Syntax.Import.path
d_path_90 ::
  T_Import_84 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_90 v0
  = case coe v0 of
      C_mkImport_94 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Import.alias
d_alias_92 ::
  T_Import_84 -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_alias_92 v0
  = case coe v0 of
      C_mkImport_94 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Decl
d_Decl_96 = ()
data T_Decl_96
  = C_DTypeSig_98 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  T_PolyType_10 |
    C_DFunDef_100 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  T_Expr_44 |
    C_DSignature_102 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_PolyType_10 |
    C_DTypeAlias_104 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_PolyType_10 |
    C_DImport_106 T_Import_84
-- Once.Spec.Surface.Syntax.Module
d_Module_108 = ()
newtype T_Module_108 = C_mkModule_114 [T_Decl_96]
-- Once.Spec.Surface.Syntax.Module.decls
d_decls_112 :: T_Module_108 -> [T_Decl_96]
d_decls_112 v0
  = case coe v0 of
      C_mkModule_114 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
