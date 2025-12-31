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

module MAlonzo.Code.Once.TypeCheck where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Infer
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.typeCheck
d_typeCheck_4 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Infer.T_InferResult_142
d_typeCheck_4 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Infer.d_infer_148
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24) (coe v0)
      (coe (0 :: Integer))
-- Once.TypeCheck.typeCheckAgainst
d_typeCheckAgainst_8 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.TypeCheck.Infer.T_InferResult_142
d_typeCheckAgainst_8 v0 v1
  = coe
      MAlonzo.Code.Once.TypeCheck.Infer.d_check_1340
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24) (coe v0)
      (coe v1) (coe (0 :: Integer))
