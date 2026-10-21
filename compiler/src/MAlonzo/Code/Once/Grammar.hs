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

module MAlonzo.Code.Once.Grammar where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Grammar.LowerIdent
d_LowerIdent_4 :: ()
d_LowerIdent_4 = erased
-- Once.Grammar.UpperIdent
d_UpperIdent_6 :: ()
d_UpperIdent_6 = erased
-- Once.Grammar.GType
d_GType_8 = ()
data T_GType_8
  = C_TUnit_12 | C_TVoid_14 | C_TInt_16 | C_TFloat_18 |
    C__'8658''91'_'93'__20 T_GType_8
                           MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_GType_8 |
    C__'8855'__22 T_GType_8 T_GType_8 |
    C__'8853'__24 T_GType_8 T_GType_8 | C_TEff_26 T_GType_8 T_GType_8 |
    C_TAct_28 T_GType_8 T_GType_8 | C_GMu_30 T_GFunctor_10 |
    C_GNu_32 T_GFunctor_10 | C_GNuAct_34 T_GFunctor_10 |
    C_TVar_36 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Grammar.GFunctor
d_GFunctor_10 = ()
data T_GFunctor_10
  = C_GFK_38 T_GType_8 | C_GFId_40 |
    C_GFSum_42 T_GFunctor_10 T_GFunctor_10 |
    C_GFProd_44 T_GFunctor_10 T_GFunctor_10
-- Once.Grammar._⇒_
d__'8658'__46 :: T_GType_8 -> T_GType_8 -> T_GType_8
d__'8658'__46 v0 v1
  = coe
      C__'8658''91'_'93'__20 (coe v0)
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1)
-- Once.Grammar.BinOp
d_BinOp_52 = ()
data T_BinOp_52
  = C_OpAdd_54 | C_OpSub_56 | C_OpMul_58 | C_OpDiv_60 | C_OpMod_62 |
    C_OpLt_64 | C_OpLe_66 | C_OpGt_68 | C_OpGe_70 | C_OpEq_72 |
    C_OpNe_74
-- Once.Grammar.UnaryOp
d_UnaryOp_76 = ()
data T_UnaryOp_76 = C_OpNeg_78
-- Once.Grammar.GExpr
d_GExpr_80 = ()
data T_GExpr_80
  = C_EUnit_82 | C_EInt_84 Integer |
    C_EVar_86 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_88 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_90 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80 |
    C_EApp_92 T_GExpr_80 T_GExpr_80 |
    C_EPair_94 T_GExpr_80 T_GExpr_80 |
    C_ELet_96 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_80 |
    C_EDestruct_98 T_GExpr_80
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80 |
    C_EBinOp_100 T_BinOp_52 T_GExpr_80 T_GExpr_80 |
    C_EUnaryOp_102 T_GExpr_80 | C_ECompose_104 T_GExpr_80 T_GExpr_80 |
    C_EAnnot_106 T_GExpr_80 T_GType_8
-- Once.Grammar.ModulePath
d_ModulePath_108 :: ()
d_ModulePath_108 = erased
-- Once.Grammar.GDecl
d_GDecl_110 = ()
data T_GDecl_110
  = C_DTypeSig_112 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_114 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GExpr_80 |
    C_DSignature_116 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_120 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_122 = ()
newtype T_GModule_122 = C_mkGModule_128 [T_GDecl_110]
-- Once.Grammar.GModule.decls
d_decls_126 :: T_GModule_122 -> [T_GDecl_110]
d_decls_126 v0
  = case coe v0 of
      C_mkGModule_128 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_130 a0 a1 = ()
data T_ValidDeclPair_130 = C_validPair_140
-- Once.Grammar.ValidMainType
d_ValidMainType_142 a0 = ()
data T_ValidMainType_142 = C_validMain_146
