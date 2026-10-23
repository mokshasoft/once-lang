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
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Syntax.RawExpr
d_RawExpr_6 :: ()
d_RawExpr_6 = erased
-- Once.Internal.Syntax.isComparisonOp
d_isComparisonOp_8 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Bool
d_isComparisonOp_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.isFloatArithmeticOp
d_isFloatArithmeticOp_10 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Bool
d_isFloatArithmeticOp_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.isArithmeticOp
d_isArithmeticOp_12 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 -> Bool
d_isArithmeticOp_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Syntax.ClosedLiftShape
d_ClosedLiftShape_14 a0 = ()
data T_ClosedLiftShape_14
  = C_cls'45'var_18 | C_cls'45'qual_24 | C_cls'45'res_28 |
    C_cls'45'let_36 | C_cls'45'destr_48 | C_cls'45'unit_50 |
    C_cls'45'annot_56 | C_cls'45'binop_64
