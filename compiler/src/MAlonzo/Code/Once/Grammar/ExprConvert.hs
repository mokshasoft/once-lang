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

module MAlonzo.Code.Once.Grammar.ExprConvert where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ExprPrinter
import qualified MAlonzo.Code.Once.Grammar.ParserRelation
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax

-- Once.Grammar.ExprConvert.gBinOpToRaw
d_gBinOpToRaw_6 ::
  MAlonzo.Code.Once.Grammar.T_BinOp_52 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44
d_gBinOpToRaw_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_54
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
      MAlonzo.Code.Once.Grammar.C_OpSub_56
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
      MAlonzo.Code.Once.Grammar.C_OpMul_58
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
      MAlonzo.Code.Once.Grammar.C_OpDiv_60
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
      MAlonzo.Code.Once.Grammar.C_OpMod_62
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
      MAlonzo.Code.Once.Grammar.C_OpLt_64
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
      MAlonzo.Code.Once.Grammar.C_OpLe_66
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
      MAlonzo.Code.Once.Grammar.C_OpGt_68
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
      MAlonzo.Code.Once.Grammar.C_OpGe_70
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
      MAlonzo.Code.Once.Grammar.C_OpEq_72
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
      MAlonzo.Code.Once.Grammar.C_OpNe_74
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprConvert.gexprToRaw
d_gexprToRaw_10 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_gexprToRaw_10 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_78
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_82
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EInt_84 v3
               -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_86
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EVar_86 v4
               -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_92
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EQualified_88 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 (coe v5)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_98 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELam_90 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 (coe v5)
                    (coe d_gexprToRaw_10 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_104 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EApp_92 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                    (coe d_gexprToRaw_10 (coe v6) (coe v4))
                    (coe d_gexprToRaw_10 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_110 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EPair_94 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82
                    (coe d_gexprToRaw_10 (coe v6) (coe v4))
                    (coe d_gexprToRaw_10 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_116 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EAnnot_106 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92
                    (coe d_gexprToRaw_10 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_124 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EBinOp_100 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94
                    (coe d_gBinOpToRaw_6 (coe v7))
                    (coe d_gexprToRaw_10 (coe v8) (coe v5))
                    (coe d_gexprToRaw_10 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_130 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EUnaryOp_102 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96
                    (coe d_gexprToRaw_10 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_136 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ECompose_104 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76
                       (coe
                          MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70
                          (coe ("compose" :: Data.Text.Text)))
                       (coe d_gexprToRaw_10 (coe v6) (coe v4)))
                    (coe d_gexprToRaw_10 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_144 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELet_96 v7 v8
               -> case coe v7 of
                    (:) v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 (coe v11)
                                  (coe d_gexprToRaw_10 (coe v12) (coe v5))
                                  (coe d_gexprToRaw_10 (coe v8) (coe v6))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_156 v7 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EDestruct_98 v10 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84
                    (coe d_gexprToRaw_10 (coe v10) (coe v7)) (coe v11)
                    (coe d_gexprToRaw_10 (coe v12) (coe v8)) (coe v13)
                    (coe d_gexprToRaw_10 (coe v14) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
