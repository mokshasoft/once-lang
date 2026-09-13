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
      C__'8658''91'_'93'__24 (coe v0)
      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)
-- Once.Grammar.BinOp
d_BinOp_56 = ()
data T_BinOp_56
  = C_OpAdd_58 | C_OpSub_60 | C_OpMul_62 | C_OpDiv_64 | C_OpMod_66 |
    C_OpLt_68 | C_OpLe_70 | C_OpGt_72 | C_OpGe_74 | C_OpEq_76 |
    C_OpNe_78
-- Once.Grammar.UnaryOp
d_UnaryOp_80 = ()
data T_UnaryOp_80 = C_OpNeg_82
-- Once.Grammar.GExpr
d_GExpr_84 = ()
data T_GExpr_84
  = C_EUnit_86 | C_EInt_88 Integer |
    C_EString_90 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EVar_92 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_94 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_96 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_84 |
    C_EApp_98 T_GExpr_84 T_GExpr_84 |
    C_EPair_100 T_GExpr_84 T_GExpr_84 |
    C_ELet_102 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_84 |
    C_EDestruct_104 T_GExpr_84
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_84
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_84 |
    C_EBinOp_106 T_BinOp_56 T_GExpr_84 T_GExpr_84 |
    C_EUnaryOp_108 T_GExpr_84 | C_ECompose_110 T_GExpr_84 T_GExpr_84 |
    C_EAnnot_112 T_GExpr_84 T_GType_8
-- Once.Grammar.ModulePath
d_ModulePath_114 :: ()
d_ModulePath_114 = erased
-- Once.Grammar.GDecl
d_GDecl_116 = ()
data T_GDecl_116
  = C_DTypeSig_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_120 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GExpr_84 |
    C_DSignature_122 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_124 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_126 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_128 = ()
newtype T_GModule_128 = C_mkGModule_134 [T_GDecl_116]
-- Once.Grammar.GModule.decls
d_decls_132 :: T_GModule_128 -> [T_GDecl_116]
d_decls_132 v0
  = case coe v0 of
      C_mkGModule_134 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_136 a0 a1 = ()
data T_ValidDeclPair_136 = C_validPair_146
-- Once.Grammar.ValidMainType
d_ValidMainType_148 a0 = ()
data T_ValidMainType_148 = C_validMain_152
