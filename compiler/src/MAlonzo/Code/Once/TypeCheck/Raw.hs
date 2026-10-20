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
import qualified MAlonzo.Code.Once.Lang.Syntax

-- Once.TypeCheck.Raw.closedLiftShape?
d_closedLiftShape'63'_8 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Lang.Syntax.T_ClosedLiftShape_72
d_closedLiftShape'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'var_76)
      MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'qual_82)
      MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'res_86)
      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'let_94)
      MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'destr_106)
      MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'unit_108)
      MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'annot_114)
      MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Syntax.C_cls'45'binop_122)
      MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Syntax.C_RAna_64 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.closedLiftShape?-just
d_closedLiftShape'63''45'just_14 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_ClosedLiftShape_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closedLiftShape'63''45'just_14 = erased
