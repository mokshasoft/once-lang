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
import qualified MAlonzo.Code.Once.Type

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
    C_TBuffer_20 | C_TString_22 |
    C__'8658''91'_'93'__24 T_GType_8
                           MAlonzo.Code.Once.Type.T_Quantity_4 T_GType_8 |
    C__'8855'__26 T_GType_8 T_GType_8 |
    C__'8853'__28 T_GType_8 T_GType_8 | C_TEff_30 T_GType_8 T_GType_8 |
    C_GMu_32 T_GFunctor_10 | C_GNu_34 T_GFunctor_10 |
    C_GNuEff_36 T_GFunctor_10 |
    C_TVar_38 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Grammar.GFunctor
d_GFunctor_10 = ()
data T_GFunctor_10
  = C_GFK_40 T_GType_8 | C_GFId_42 |
    C_GFSum_44 T_GFunctor_10 T_GFunctor_10 |
    C_GFProd_46 T_GFunctor_10 T_GFunctor_10
-- Once.Grammar._⇒_
d__'8658'__48 :: T_GType_8 -> T_GType_8 -> T_GType_8
d__'8658'__48 v0 v1
  = coe
      C__'8658''91'_'93'__24 (coe v0)
      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)
-- Once.Grammar.BinOp
d_BinOp_58 = ()
data T_BinOp_58
  = C_OpAdd_60 | C_OpSub_62 | C_OpMul_64 | C_OpDiv_66 | C_OpMod_68 |
    C_OpLt_70 | C_OpLe_72 | C_OpGt_74 | C_OpGe_76 | C_OpEq_78 |
    C_OpNe_80
-- Once.Grammar.UnaryOp
d_UnaryOp_82 = ()
data T_UnaryOp_82 = C_OpNeg_84
-- Once.Grammar.GExpr
d_GExpr_86 = ()
data T_GExpr_86
  = C_EUnit_88 | C_EInt_90 Integer |
    C_EString_92 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EVar_94 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_96 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_98 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_86 |
    C_EApp_100 T_GExpr_86 T_GExpr_86 |
    C_EPair_102 T_GExpr_86 T_GExpr_86 |
    C_ELet_104 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_86 |
    C_EDestruct_106 T_GExpr_86
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_86
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_86 |
    C_EBinOp_108 T_BinOp_58 T_GExpr_86 T_GExpr_86 |
    C_EUnaryOp_110 T_GExpr_86 | C_ECompose_112 T_GExpr_86 T_GExpr_86 |
    C_EAnnot_114 T_GExpr_86 T_GType_8
-- Once.Grammar.ModulePath
d_ModulePath_116 :: ()
d_ModulePath_116 = erased
-- Once.Grammar.GDecl
d_GDecl_118 = ()
data T_GDecl_118
  = C_DTypeSig_120 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_122 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GExpr_86 |
    C_DSignature_124 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_126 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_128 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_130 = ()
newtype T_GModule_130 = C_mkGModule_136 [T_GDecl_118]
-- Once.Grammar.GModule.decls
d_decls_134 :: T_GModule_130 -> [T_GDecl_118]
d_decls_134 v0
  = case coe v0 of
      C_mkGModule_136 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_138 a0 a1 = ()
data T_ValidDeclPair_138 = C_validPair_148
-- Once.Grammar.ValidMainType
d_ValidMainType_150 a0 = ()
data T_ValidMainType_150 = C_validMain_154
