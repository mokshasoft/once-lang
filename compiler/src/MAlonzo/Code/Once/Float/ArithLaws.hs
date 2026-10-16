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

module MAlonzo.Code.Once.Float.ArithLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Float.ArithLaws.≡ᵇ-sym
d_'8801''7495''45'sym_94 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'sym_94 = erased
-- Once.Float.ArithLaws.+B-comm
d_'43'B'45'comm_104 ::
  MAlonzo.Code.Once.Spec.Float.Arith.T_Bin_8 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Bin_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'B'45'comm_104 = erased
-- Once.Float.ArithLaws.*B-comm
d_'42'B'45'comm_124 ::
  MAlonzo.Code.Once.Spec.Float.Arith.T_Bin_8 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_Bin_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42'B'45'comm_124 = erased
-- Once.Float.ArithLaws.addV-inf-aux
d_addV'45'inf'45'aux_142 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addV'45'inf'45'aux_142 = erased
-- Once.Float.ArithLaws.addV-comm
d_addV'45'comm_164 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_FloatVal_56 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_FloatVal_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addV'45'comm_164 = erased
-- Once.Float.ArithLaws.xorS-comm
d_xorS'45'comm_204 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xorS'45'comm_204 = erased
-- Once.Float.ArithLaws.mulV-inf-fin-aux
d_mulV'45'inf'45'fin'45'aux_222 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mulV'45'inf'45'fin'45'aux_222 = erased
-- Once.Float.ArithLaws.mulV-comm
d_mulV'45'comm_242 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_FloatVal_56 ->
  MAlonzo.Code.Once.Spec.Float.Arith.T_FloatVal_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mulV'45'comm_242 = erased
-- Once.Float.ArithLaws.fadd-comm
d_fadd'45'comm_284 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fadd'45'comm_284 = erased
-- Once.Float.ArithLaws.fmul-comm
d_fmul'45'comm_298 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmul'45'comm_298 = erased
