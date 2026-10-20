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
import qualified MAlonzo.Code.Once.Lang.Syntax

-- Once.Grammar.ExprConvert.gBinOpToRaw
d_gBinOpToRaw_6 ::
  MAlonzo.Code.Once.Grammar.T_BinOp_52 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6
d_gBinOpToRaw_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_54
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
      MAlonzo.Code.Once.Grammar.C_OpSub_56
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
      MAlonzo.Code.Once.Grammar.C_OpMul_58
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
      MAlonzo.Code.Once.Grammar.C_OpDiv_60
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
      MAlonzo.Code.Once.Grammar.C_OpMod_62
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16
      MAlonzo.Code.Once.Grammar.C_OpLt_64
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18
      MAlonzo.Code.Once.Grammar.C_OpLe_66
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20
      MAlonzo.Code.Once.Grammar.C_OpGt_68
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22
      MAlonzo.Code.Once.Grammar.C_OpGe_70
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24
      MAlonzo.Code.Once.Grammar.C_OpEq_72
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26
      MAlonzo.Code.Once.Grammar.C_OpNe_74
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprConvert.gUnaryOpToRaw
d_gUnaryOpToRaw_8 ::
  MAlonzo.Code.Once.Grammar.T_UnaryOp_76 ->
  MAlonzo.Code.Once.Lang.Syntax.T_UnaryOp_30
d_gUnaryOpToRaw_8 = erased
-- Once.Grammar.ExprConvert.gexprToRaw
d_gexprToRaw_12 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_80 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_76 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
d_gexprToRaw_12 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_78
        -> coe MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_82
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EInt_84 v3
               -> coe MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_86
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EVar_86 v4
               -> coe MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_92
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EQualified_88 v5 v6
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_98 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELam_90 v5 v6
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 (coe v5)
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_104 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EApp_92 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_110 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EPair_94 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RPair_48
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_116 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EAnnot_106 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_124 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EBinOp_100 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60
                    (coe d_gBinOpToRaw_6 (coe v7))
                    (coe d_gexprToRaw_12 (coe v8) (coe v5))
                    (coe d_gexprToRaw_12 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_130 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EUnaryOp_102 v6
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62
                    (d_gexprToRaw_12 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_136 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ECompose_104 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                    (coe
                       MAlonzo.Code.Once.Lang.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Lang.Syntax.C_RVar_36
                          (coe ("compose" :: Data.Text.Text)))
                       (coe d_gexprToRaw_12 (coe v6) (coe v4)))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_144 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELet_96 v7 v8
               -> case coe v7 of
                    (:) v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 (coe v11)
                                  (coe d_gexprToRaw_12 (coe v12) (coe v5))
                                  (coe d_gexprToRaw_12 (coe v8) (coe v6))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_156 v7 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EDestruct_98 v10 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50
                    (coe d_gexprToRaw_12 (coe v10) (coe v7)) (coe v11)
                    (coe d_gexprToRaw_12 (coe v12) (coe v8)) (coe v13)
                    (coe d_gexprToRaw_12 (coe v14) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
