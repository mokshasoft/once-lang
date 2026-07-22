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

module MAlonzo.Code.Once.Arith.Backend.Adequacy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Target.RegConvention

-- Once.Arith.Backend.Adequacy.ArithEmitConfined
d_ArithEmitConfined_10 a0 = ()
data T_ArithEmitConfined_10
  = C_constructor_54 (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
                      [AgdaAny])
                     (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
                      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44)
-- Once.Arith.Backend.Adequacy.ArithEmitConfined.writes
d_writes_46 ::
  T_ArithEmitConfined_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  [AgdaAny]
d_writes_46 v0
  = case coe v0 of
      C_constructor_54 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Adequacy.ArithEmitConfined.confined
d_confined_52 ::
  T_ArithEmitConfined_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_confined_52 v0
  = case coe v0 of
      C_constructor_54 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
