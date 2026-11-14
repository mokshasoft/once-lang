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

module MAlonzo.Code.Once.Surface.Numeric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Surface.Numeric.toFloatIR
d_toFloatIR_6 :: MAlonzo.Code.Once.IR.T_IR_16
d_toFloatIR_6
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136)
-- Once.Surface.Numeric.numBin
d_numBin_22 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_numBin_22 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_numBin_22 v3 v4 v5 v6 v7 v8 v9
du_numBin_22 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_numBin_22 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_num_216 v3
      (MAlonzo.Code.Once.Spec.Surface.Operator.d_theory_60
         (coe MAlonzo.Code.Once.Spec.Surface.Operator.d_binSym_68 (coe v2)))
      (MAlonzo.Code.Once.Spec.Surface.Operator.d_shape_62
         (coe MAlonzo.Code.Once.Spec.Surface.Operator.d_binSym_68 (coe v2)))
      v4
      (MAlonzo.Code.Once.Spec.Surface.Operator.d_symbol_64
         (coe MAlonzo.Code.Once.Spec.Surface.Operator.d_binSym_68 (coe v2)))
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v0 v1 v5 v6)
