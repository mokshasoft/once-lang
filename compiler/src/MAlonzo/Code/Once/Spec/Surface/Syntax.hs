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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
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
-- Once.Spec.Surface.Syntax.BinOp
d_BinOp_44 = ()
data T_BinOp_44
  = C_OpAdd_46 | C_OpSub_48 | C_OpMul_50 | C_OpDiv_52 | C_OpMod_54 |
    C_OpLt_56 | C_OpLe_58 | C_OpGt_60 | C_OpGe_62 | C_OpEq_64 |
    C_OpNe_66
-- Once.Spec.Surface.Syntax.Expr
d_Expr_68 = ()
data T_Expr_68
  = C_RVar_70 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RQualified_72 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RResolved_74 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_RApp_76 T_Expr_68 T_Expr_68 |
    C_RLam_78 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_68 |
    C_RLet_80 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_68
              T_Expr_68 |
    C_RPair_82 T_Expr_68 T_Expr_68 |
    C_RDestruct_84 T_Expr_68
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_68
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_Expr_68 |
    C_RUnit_86 | C_RInt_88 Integer |
    C_RFloat_90 Integer Integer Integer |
    C_RAnnot_92 T_Expr_68 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_RBinOp_94 T_BinOp_44 T_Expr_68 T_Expr_68 | C_RNeg_96 T_Expr_68
-- Once.Spec.Surface.Syntax.Import
d_Import_98 = ()
data T_Import_98
  = C_mkImport_108 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                   (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Spec.Surface.Syntax.Import.path
d_path_104 ::
  T_Import_98 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_104 v0
  = case coe v0 of
      C_mkImport_108 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Import.alias
d_alias_106 ::
  T_Import_98 -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_alias_106 v0
  = case coe v0 of
      C_mkImport_108 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Syntax.Decl
d_Decl_110 = ()
data T_Decl_110
  = C_DTypeSig_112 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_PolyType_10 |
    C_DFunDef_114 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  T_Expr_68 |
    C_DSignature_116 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_PolyType_10 |
    C_DTypeAlias_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_PolyType_10 |
    C_DImport_120 T_Import_98
-- Once.Spec.Surface.Syntax.Module
d_Module_122 = ()
newtype T_Module_122 = C_mkModule_128 [T_Decl_110]
-- Once.Spec.Surface.Syntax.Module.decls
d_decls_126 :: T_Module_122 -> [T_Decl_110]
d_decls_126 v0
  = case coe v0 of
      C_mkModule_128 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
