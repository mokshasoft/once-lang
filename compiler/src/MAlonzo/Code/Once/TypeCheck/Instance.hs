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

module MAlonzo.Code.Once.TypeCheck.Instance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.Schema
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Instance
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Once.Spec.Typing
import qualified MAlonzo.Code.Once.Spec.Typing.Scope
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.RigidSubst

-- Once.TypeCheck.Instance.inst-at
d_inst'45'at_24 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
d_inst'45'at_24 v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_inst'45'at_24 v0 v1 v2 v3 v4 v5 v7
du_inst'45'at_24 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
du_inst'45'at_24 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.d_subst'45'c_534
      (coe MAlonzo.Code.Once.Spec.Type.Instance.d_arityOf_84 (coe v3))
      (coe MAlonzo.Code.Once.Spec.Core.Schema.d_kindsOf_352 (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Spec.Core.Schema.du_kinded'45'instance_778
            (coe v3) (coe v6)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Spec.Core.Schema.du_kinded'45'instance_778
               (coe v3) (coe v6))))
      (coe
         MAlonzo.Code.Once.Spec.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
         (coe v1)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
      (coe v2)
      (coe MAlonzo.Code.Once.Spec.Type.Instance.d_rigidOf_126 (coe v3))
      (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_48) (coe v4)
      (coe v5)
