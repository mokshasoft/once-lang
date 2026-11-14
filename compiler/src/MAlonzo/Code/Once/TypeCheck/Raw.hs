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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.TypeCheck.Raw.ClosedLiftShape
d_ClosedLiftShape_6 a0 = ()
data T_ClosedLiftShape_6
  = C_cls'45'var_10 | C_cls'45'qual_16 | C_cls'45'res_20 |
    C_cls'45'let_28 | C_cls'45'destr_40 | C_cls'45'unit_42 |
    C_cls'45'annot_48 | C_cls'45'binop_56
-- Once.TypeCheck.Raw.closedLiftShape?
d_closedLiftShape'63'_60 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  Maybe T_ClosedLiftShape_6
d_closedLiftShape'63'_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'var_10)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_48 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'qual_16)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'res_20)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_56 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'let_28)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_60 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'destr_40)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_62
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'unit_42)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_64 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_66 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_68 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'annot_48)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_70 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_cls'45'binop_56)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Raw.closedLiftShape?-just
d_closedLiftShape'63''45'just_66 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_ClosedLiftShape_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closedLiftShape'63''45'just_66 = erased
