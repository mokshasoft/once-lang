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
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax

-- Once.TypeCheck.Raw.closedLiftShape?
d_closedLiftShape'63'_8 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14
d_closedLiftShape'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'var_18)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'qual_24)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'res_28)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'let_36)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'destr_48)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'unit_50)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'annot_56)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Syntax.C_cls'45'binop_64)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.closedLiftShape?-just
d_closedLiftShape'63''45'just_14 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Internal.Syntax.T_ClosedLiftShape_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closedLiftShape'63''45'just_14 = erased
