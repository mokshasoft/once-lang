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

module MAlonzo.Code.Once.Grammar.ExprRoundtrip where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ExprPrinter

-- Once.Grammar.ExprRoundtrip.round-trip-EUnit
d_round'45'trip'45'EUnit_6 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EUnit_6 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EInt-0
d_round'45'trip'45'EInt'45'0_8 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EInt'45'0_8 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EInt-42
d_round'45'trip'45'EInt'45'42_10 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EInt'45'42_10 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EString
d_round'45'trip'45'EString_12 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EString_12 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EVar-x
d_round'45'trip'45'EVar'45'x_14 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EVar'45'x_14 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EVar-foo
d_round'45'trip'45'EVar'45'foo_16 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EVar'45'foo_16 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EQualified
d_round'45'trip'45'EQualified_18 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EQualified_18 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EPair-vars
d_round'45'trip'45'EPair'45'vars_20 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EPair'45'vars_20 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-ENeg-var
d_round'45'trip'45'ENeg'45'var_22 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'ENeg'45'var_22 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-ELam-id
d_round'45'trip'45'ELam'45'id_24 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'ELam'45'id_24 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EApp-vars
d_round'45'trip'45'EApp'45'vars_26 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EApp'45'vars_26 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EBinOp-add
d_round'45'trip'45'EBinOp'45'add_28 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EBinOp'45'add_28 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EBinOp-mul
d_round'45'trip'45'EBinOp'45'mul_30 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EBinOp'45'mul_30 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-ECompose-vars
d_round'45'trip'45'ECompose'45'vars_32 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'ECompose'45'vars_32 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-ELet-simple
d_round'45'trip'45'ELet'45'simple_34 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'ELet'45'simple_34 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EDestruct
d_round'45'trip'45'EDestruct_36 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EDestruct_36 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EPair-nested
d_round'45'trip'45'EPair'45'nested_38 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EPair'45'nested_38 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EBinOp-lt
d_round'45'trip'45'EBinOp'45'lt_40 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EBinOp'45'lt_40 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EBinOp-sub
d_round'45'trip'45'EBinOp'45'sub_42 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EBinOp'45'sub_42 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EApp-two-args
d_round'45'trip'45'EApp'45'two'45'args_44 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EApp'45'two'45'args_44 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EInt
d_round'45'trip'45'EInt_48 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EInt_48 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-EString-gen
d_round'45'trip'45'EString'45'gen_54 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'EString'45'gen_54 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-c-e-unit
d_round'45'trip'45'c'45'e'45'unit_58 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'c'45'e'45'unit_58 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-c-e-int
d_round'45'trip'45'c'45'e'45'int_62 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'c'45'e'45'int_62 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-c-e-string
d_round'45'trip'45'c'45'e'45'string_66 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'c'45'e'45'string_66 = erased
-- Once.Grammar.ExprRoundtrip.round-trip-concrete-expr
d_round'45'trip'45'concrete'45'expr_72 ::
  MAlonzo.Code.Once.Grammar.T_GExpr_82 ->
  MAlonzo.Code.Once.Grammar.ExprPrinter.T_ConcreteExpr_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_round'45'trip'45'concrete'45'expr_72 = erased
