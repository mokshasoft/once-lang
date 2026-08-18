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
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Grammar.ExprConvert.gBinOpToRaw
d_gBinOpToRaw_6 ::
  MAlonzo.Code.Once.Grammar.T_BinOp_54 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6
d_gBinOpToRaw_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_OpAdd_56
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
      MAlonzo.Code.Once.Grammar.C_OpSub_58
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
      MAlonzo.Code.Once.Grammar.C_OpMul_60
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
      MAlonzo.Code.Once.Grammar.C_OpDiv_62
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
      MAlonzo.Code.Once.Grammar.C_OpMod_64
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
      MAlonzo.Code.Once.Grammar.C_OpLt_66
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
      MAlonzo.Code.Once.Grammar.C_OpLe_68
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
      MAlonzo.Code.Once.Grammar.C_OpGt_70
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
      MAlonzo.Code.Once.Grammar.C_OpGe_72
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
      MAlonzo.Code.Once.Grammar.C_OpEq_74
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
      MAlonzo.Code.Once.Grammar.C_OpNe_76
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ExprConvert.gUnaryOpToRaw
d_gUnaryOpToRaw_8 ::
  MAlonzo.Code.Once.Grammar.T_UnaryOp_78 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30
d_gUnaryOpToRaw_8 = erased
-- Once.Grammar.ExprConvert.gexprToRaw
d_gexprToRaw_12 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_82 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_gexprToRaw_12 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unit_80
        -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'int_84
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EInt_86 v3
               -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'string_88
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EString_88 v3
               -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'var_92
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EVar_90 v4
               -> coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'qual_98
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EQualified_92 v5 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'lam_104 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELam_94 v5 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 (coe v5)
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'app_110 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EApp_96 v6 v7
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'pair_116 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EPair_98 v6 v7
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'annot_122 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EAnnot_110 v6 v7
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60
                    (coe d_gexprToRaw_12 (coe v6) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Grammar.ParserRelation.d_toType_8 (coe v7)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'binop_130 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EBinOp_104 v7 v8 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62
                    (coe d_gBinOpToRaw_6 (coe v7))
                    (coe d_gexprToRaw_12 (coe v8) (coe v5))
                    (coe d_gexprToRaw_12 (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'unary_136 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EUnaryOp_106 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64
                    (d_gexprToRaw_12 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'comp_142 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ECompose_108 v6 v7
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                          (coe ("compose" :: Data.Text.Text)))
                       (coe d_gexprToRaw_12 (coe v6) (coe v4)))
                    (coe d_gexprToRaw_12 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'let1_150 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_ELet_100 v7 v8
               -> case coe v7 of
                    (:) v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 (coe v11)
                                  (coe d_gexprToRaw_12 (coe v12) (coe v5))
                                  (coe d_gexprToRaw_12 (coe v8) (coe v6))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Grammar.ExprPrinter.C_c'45'e'45'destr_162 v7 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Grammar.C_EDestruct_102 v10 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50
                    (coe d_gexprToRaw_12 (coe v10) (coe v7)) (coe v11)
                    (coe d_gexprToRaw_12 (coe v12) (coe v8)) (coe v13)
                    (coe d_gexprToRaw_12 (coe v14) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
