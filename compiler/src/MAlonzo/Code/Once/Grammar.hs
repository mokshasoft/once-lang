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
    C_GMu_32 T_GFunctor_10 |
    C_TVar_34 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Grammar.GFunctor
d_GFunctor_10 = ()
data T_GFunctor_10
  = C_GFK_36 T_GType_8 | C_GFId_38 |
    C_GFSum_40 T_GFunctor_10 T_GFunctor_10 |
    C_GFProd_42 T_GFunctor_10 T_GFunctor_10
-- Once.Grammar._⇒_
d__'8658'__44 :: T_GType_8 -> T_GType_8 -> T_GType_8
d__'8658'__44 v0 v1
  = coe
      C__'8658''91'_'93'__24 (coe v0)
      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)
-- Once.Grammar.BinOp
d_BinOp_54 = ()
data T_BinOp_54
  = C_OpAdd_56 | C_OpSub_58 | C_OpMul_60 | C_OpDiv_62 | C_OpMod_64 |
    C_OpLt_66 | C_OpLe_68 | C_OpGt_70 | C_OpGe_72 | C_OpEq_74 |
    C_OpNe_76
-- Once.Grammar.UnaryOp
d_UnaryOp_78 = ()
data T_UnaryOp_78 = C_OpNeg_80
-- Once.Grammar.GExpr
d_GExpr_82 = ()
data T_GExpr_82
  = C_EUnit_84 | C_EInt_86 Integer |
    C_EString_88 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EVar_90 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_92 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_94 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_82 |
    C_EApp_96 T_GExpr_82 T_GExpr_82 |
    C_EPair_98 T_GExpr_82 T_GExpr_82 |
    C_ELet_100 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_82 |
    C_EDestruct_102 T_GExpr_82
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_82
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_82 |
    C_EBinOp_104 T_BinOp_54 T_GExpr_82 T_GExpr_82 |
    C_EUnaryOp_106 T_GExpr_82 | C_ECompose_108 T_GExpr_82 T_GExpr_82 |
    C_EAnnot_110 T_GExpr_82 T_GType_8
-- Once.Grammar.AllocStrategy
d_AllocStrategy_112 = ()
data T_AllocStrategy_112
  = C_Stack_114 | C_Arena_116 | C_Pool_118 | C_Heap_120 | C_Const_122
-- Once.Grammar.ModulePath
d_ModulePath_124 :: ()
d_ModulePath_124 = erased
-- Once.Grammar.GDecl
d_GDecl_126 = ()
data T_GDecl_126
  = C_DTypeSig_128 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_130 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe T_AllocStrategy_112) T_GExpr_82 |
    C_DSignature_132 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_134 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_136 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_138 = ()
newtype T_GModule_138 = C_mkGModule_144 [T_GDecl_126]
-- Once.Grammar.GModule.decls
d_decls_142 :: T_GModule_138 -> [T_GDecl_126]
d_decls_142 v0
  = case coe v0 of
      C_mkGModule_144 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_146 a0 a1 = ()
data T_ValidDeclPair_146 = C_validPair_158
-- Once.Grammar.ValidMainType
d_ValidMainType_160 a0 = ()
data T_ValidMainType_160 = C_validMain_164
