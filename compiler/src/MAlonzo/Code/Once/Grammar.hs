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
  = C_TUnit_10 | C_TVoid_12 | C_TInt_14 | C_TFloat_16 |
    C_TBuffer_18 | C_TString_20 |
    C__'8658''91'_'93'__22 T_GType_8
                           MAlonzo.Code.Once.Type.T_Quantity_4 T_GType_8 |
    C__'8855'__24 T_GType_8 T_GType_8 |
    C__'8853'__26 T_GType_8 T_GType_8 | C_TEff_28 T_GType_8 T_GType_8 |
    C_TVar_30 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Grammar._⇒_
d__'8658'__32 :: T_GType_8 -> T_GType_8 -> T_GType_8
d__'8658'__32 v0 v1
  = coe
      C__'8658''91'_'93'__22 (coe v0)
      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)
-- Once.Grammar.BinOp
d_BinOp_42 = ()
data T_BinOp_42
  = C_OpAdd_44 | C_OpSub_46 | C_OpMul_48 | C_OpDiv_50 | C_OpMod_52 |
    C_OpLt_54 | C_OpLe_56 | C_OpGt_58 | C_OpGe_60 | C_OpEq_62 |
    C_OpNe_64
-- Once.Grammar.UnaryOp
d_UnaryOp_66 = ()
data T_UnaryOp_66 = C_OpNeg_68
-- Once.Grammar.GExpr
d_GExpr_70 = ()
data T_GExpr_70
  = C_EUnit_72 | C_EInt_74 Integer |
    C_EString_76 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EVar_78 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_80 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_82 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_70 |
    C_EApp_84 T_GExpr_70 T_GExpr_70 |
    C_EPair_86 T_GExpr_70 T_GExpr_70 |
    C_ELet_88 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_70 |
    C_EDestruct_90 T_GExpr_70
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_70
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_70 |
    C_EBinOp_92 T_BinOp_42 T_GExpr_70 T_GExpr_70 |
    C_EUnaryOp_94 T_GExpr_70 | C_ECompose_96 T_GExpr_70 T_GExpr_70 |
    C_EAnnot_98 T_GExpr_70 T_GType_8
-- Once.Grammar.AllocStrategy
d_AllocStrategy_100 = ()
data T_AllocStrategy_100
  = C_Stack_102 | C_Arena_104 | C_Pool_106 | C_Heap_108 | C_Const_110
-- Once.Grammar.ModulePath
d_ModulePath_112 :: ()
d_ModulePath_112 = erased
-- Once.Grammar.GDecl
d_GDecl_114 = ()
data T_GDecl_114
  = C_DTypeSig_116 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe T_AllocStrategy_100) T_GExpr_70 |
    C_DSignature_120 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_122 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_124 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_126 = ()
newtype T_GModule_126 = C_mkGModule_132 [T_GDecl_114]
-- Once.Grammar.GModule.decls
d_decls_130 :: T_GModule_126 -> [T_GDecl_114]
d_decls_130 v0
  = case coe v0 of
      C_mkGModule_132 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_134 a0 a1 = ()
data T_ValidDeclPair_134 = C_validPair_146
-- Once.Grammar.ValidMainType
d_ValidMainType_148 a0 = ()
data T_ValidMainType_148 = C_validMain_152
