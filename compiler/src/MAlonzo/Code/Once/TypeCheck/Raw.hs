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

module MAlonzo.Code.Once.TypeCheck.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.Internal.Syntax

-- Once.TypeCheck.Raw.closedLiftShape?
d_closedLiftShape'63'_8 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  Maybe MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_66
d_closedLiftShape'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Syntax.C_RVar_32 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'var_70)
      MAlonzo.Code.Once.Internal.Syntax.C_RQualified_34 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'qual_76)
      MAlonzo.Code.Once.Internal.Syntax.C_RResolved_36 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_80)
      MAlonzo.Code.Once.Internal.Syntax.C_RApp_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Syntax.C_RLam_40 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Syntax.C_RLet_42 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'let_88)
      MAlonzo.Code.Once.Internal.Syntax.C_RPair_44 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_46 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'destr_100)
      MAlonzo.Code.Once.Internal.Syntax.C_RUnit_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'unit_102)
      MAlonzo.Code.Once.Internal.Syntax.C_RInt_50 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Syntax.C_RFloat_52 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_54 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'annot_108)
      MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_56 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'binop_116)
      MAlonzo.Code.Once.Internal.Syntax.C_RNeg_58 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.closedLiftShape?-just
d_closedLiftShape'63''45'just_14 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closedLiftShape'63''45'just_14 = erased
