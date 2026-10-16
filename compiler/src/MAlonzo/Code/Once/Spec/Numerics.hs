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

module MAlonzo.Code.Once.Spec.Numerics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic

-- Once.Spec.Numerics.TargetNum
d_TargetNum_6 = ()
data T_TargetNum_6
  = C_mkTargetNum_20 Integer
                     MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Spec.Numerics.TargetNum.int-bits
d_int'45'bits_14 :: T_TargetNum_6 -> Integer
d_int'45'bits_14 v0
  = case coe v0 of
      C_mkTargetNum_20 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Numerics.TargetNum.float-format
d_float'45'format_16 ::
  T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_float'45'format_16 v0
  = case coe v0 of
      C_mkTargetNum_20 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Numerics.TargetNum.int-bits-pos
d_int'45'bits'45'pos_18 ::
  T_TargetNum_6 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_int'45'bits'45'pos_18 v0
  = case coe v0 of
      C_mkTargetNum_20 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
