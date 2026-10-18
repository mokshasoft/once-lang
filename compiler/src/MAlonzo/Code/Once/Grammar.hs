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
import qualified MAlonzo.Code.Once.Lang.Type.Grade

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
                           MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 T_GType_8 |
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
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)
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
    C_EString_86 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EVar_88 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_EQualified_90 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_ELam_92 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80 |
    C_EApp_94 T_GExpr_80 T_GExpr_80 |
    C_EPair_96 T_GExpr_80 T_GExpr_80 |
    C_ELet_98 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] T_GExpr_80 |
    C_EDestruct_100 T_GExpr_80
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 T_GExpr_80 |
    C_EBinOp_102 T_BinOp_52 T_GExpr_80 T_GExpr_80 |
    C_EUnaryOp_104 T_GExpr_80 | C_ECompose_106 T_GExpr_80 T_GExpr_80 |
    C_EAnnot_108 T_GExpr_80 T_GType_8
-- Once.Grammar.ModulePath
d_ModulePath_110 :: ()
d_ModulePath_110 = erased
-- Once.Grammar.GDecl
d_GDecl_112 = ()
data T_GDecl_112
  = C_DTypeSig_114 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   T_GType_8 |
    C_DFunDef_116 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GExpr_80 |
    C_DSignature_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     T_GType_8 |
    C_DTypeAlias_120 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_GType_8 |
    C_DImport_122 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Grammar.GModule
d_GModule_124 = ()
newtype T_GModule_124 = C_mkGModule_130 [T_GDecl_112]
-- Once.Grammar.GModule.decls
d_decls_128 :: T_GModule_124 -> [T_GDecl_112]
d_decls_128 v0
  = case coe v0 of
      C_mkGModule_130 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ValidDeclPair
d_ValidDeclPair_132 a0 a1 = ()
data T_ValidDeclPair_132 = C_validPair_142
-- Once.Grammar.ValidMainType
d_ValidMainType_144 a0 = ()
data T_ValidMainType_144 = C_validMain_148
