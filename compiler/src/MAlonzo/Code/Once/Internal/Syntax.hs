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

module MAlonzo.Code.Once.Internal.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Syntax.BinOp
d_BinOp_6 = ()
data T_BinOp_6
  = C_OpAdd_8 | C_OpSub_10 | C_OpMul_12 | C_OpDiv_14 | C_OpMod_16 |
    C_OpLt_18 | C_OpLe_20 | C_OpGt_22 | C_OpGe_24 | C_OpEq_26 |
    C_OpNe_28
-- Once.Internal.Syntax.UnaryOp
d_UnaryOp_30 = ()
data T_UnaryOp_30 = C_OpNeg_32
-- Once.Internal.Syntax.RawExpr
d_RawExpr_34 = ()
data T_RawExpr_34
  = C_RVar_36 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RQualified_38 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_RResolved_40 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_RApp_42 T_RawExpr_34 T_RawExpr_34 |
    C_RLam_44 MAlonzo.Code.Agda.Builtin.String.T_String_6
              T_RawExpr_34 |
    C_RLet_46 MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
              T_RawExpr_34 |
    C_RPair_48 T_RawExpr_34 T_RawExpr_34 |
    C_RDestruct_50 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34
                   MAlonzo.Code.Agda.Builtin.String.T_String_6 T_RawExpr_34 |
    C_RUnit_52 | C_RInt_54 Integer |
    C_RFloat_56 Integer Integer Integer |
    C_RAnnot_58 T_RawExpr_34 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_RBinOp_60 T_BinOp_6 T_RawExpr_34 T_RawExpr_34 |
    C_RUnaryOp_62 T_RawExpr_34
-- Once.Internal.Syntax.isComparisonOp
d_isComparisonOp_64 :: T_BinOp_6 -> Bool
d_isComparisonOp_64 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.isFloatArithmeticOp
d_isFloatArithmeticOp_66 :: T_BinOp_6 -> Bool
d_isFloatArithmeticOp_66 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.isArithmeticOp
d_isArithmeticOp_68 :: T_BinOp_6 -> Bool
d_isArithmeticOp_68 v0
  = case coe v0 of
      C_OpAdd_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpSub_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMul_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpDiv_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpMod_16 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_OpLt_18 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpLe_20 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGt_22 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpGe_24 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpEq_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_OpNe_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.ClosedLiftShape
d_ClosedLiftShape_70 a0 = ()
data T_ClosedLiftShape_70
  = C_cls'45'var_74 | C_cls'45'qual_80 | C_cls'45'res_84 |
    C_cls'45'let_92 | C_cls'45'destr_104 | C_cls'45'unit_106 |
    C_cls'45'annot_112 | C_cls'45'binop_120
