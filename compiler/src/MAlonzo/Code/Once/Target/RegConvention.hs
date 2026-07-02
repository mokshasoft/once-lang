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

module MAlonzo.Code.Once.Target.RegConvention where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Relation.Unary.All

-- Once.Target.RegConvention.RegClass
d_RegClass_6 = ()
data T_RegClass_6 = C_io_8 | C_ccc_10 | C_arith_12 | C_free_14
-- Once.Target.RegConvention.RegConvention
d_RegConvention_16 = ()
data T_RegConvention_16
  = C_constructor_42 (AgdaAny ->
                      MAlonzo.Code.Agda.Builtin.String.T_String_6)
                     (AgdaAny -> T_RegClass_6) [AgdaAny]
                     MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Target.RegConvention.RegConvention.Reg
d_Reg_30 :: T_RegConvention_16 -> ()
d_Reg_30 = erased
-- Once.Target.RegConvention.RegConvention.showReg
d_showReg_32 ::
  T_RegConvention_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_32 v0
  = case coe v0 of
      C_constructor_42 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.RegConvention.RegConvention.owner
d_owner_34 :: T_RegConvention_16 -> AgdaAny -> T_RegClass_6
d_owner_34 v0
  = case coe v0 of
      C_constructor_42 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.RegConvention.RegConvention.arith-budget
d_arith'45'budget_36 :: T_RegConvention_16 -> [AgdaAny]
d_arith'45'budget_36 v0
  = case coe v0 of
      C_constructor_42 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.RegConvention.RegConvention.budget-owned
d_budget'45'owned_40 ::
  T_RegConvention_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_budget'45'owned_40 v0
  = case coe v0 of
      C_constructor_42 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
