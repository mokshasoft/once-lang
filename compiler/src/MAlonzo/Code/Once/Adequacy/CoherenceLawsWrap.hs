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

module MAlonzo.Code.Once.Adequacy.CoherenceLawsWrap where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Adequacy.CoherenceLaws
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.CoherenceLawsWrap._._≈_
d__'8776'__10 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.CoherenceLawsWrap._._≈_.≈-out
d_'8776''45'out_132 ::
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8776''45'out_132 v0
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_'8776''45'out_80
      (coe v0)
-- Once.Adequacy.CoherenceLawsWrap._.pair-cong
d_pair'45'cong_158 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_pair'45'cong_158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v11 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v13
        -> case coe v12 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v14
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_pair'45'cong'738'_202
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v13) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.add-cong
d_add'45'cong_200 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_add'45'cong_200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_add'45'cong'738'_230
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.sub-cong
d_sub'45'cong_238 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_sub'45'cong_238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_sub'45'cong'738'_258
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.mul-cong
d_mul'45'cong_276 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_mul'45'cong_276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_mul'45'cong'738'_286
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.div-cong
d_div'45'cong_314 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_div'45'cong_314 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_div'45'cong'738'_314
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.mod-cong
d_mod'45'cong_352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_mod'45'cong_352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_mod'45'cong'738'_342
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.fadd-cong
d_fadd'45'cong_390 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fadd'45'cong_390 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fadd'45'cong'738'_370
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.fsub-cong
d_fsub'45'cong_428 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fsub'45'cong_428 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fsub'45'cong'738'_398
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.fmul-cong
d_fmul'45'cong_466 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fmul'45'cong_466 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fmul'45'cong'738'_426
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.fdiv-cong
d_fdiv'45'cong_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fdiv'45'cong_504 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fdiv'45'cong'738'_454
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.lt-cong
d_lt'45'cong_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_lt'45'cong_542 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_lt'45'cong'738'_482
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.le-cong
d_le'45'cong_580 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_le'45'cong_580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_le'45'cong'738'_510
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.gt-cong
d_gt'45'cong_618 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_gt'45'cong_618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_gt'45'cong'738'_538
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.ge-cong
d_ge'45'cong_656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_ge'45'cong_656 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_ge'45'cong'738'_566
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.eq-cong
d_eq'45'cong_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_eq'45'cong_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_eq'45'cong'738'_594
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.ne-cong
d_ne'45'cong_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_ne'45'cong_732 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> case coe v10 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v12
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_ne'45'cong'738'_622
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v11) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.neg-cong
d_neg'45'cong_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_neg'45'cong_764 v0 v1 v2 ~v3 v4 v5 v6
  = du_neg'45'cong_764 v0 v1 v2 v4 v5 v6
du_neg'45'cong_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_neg'45'cong_764 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v6
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_neg'45'cong'738'_644
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.i2f-cong
d_i2f'45'cong_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_i2f'45'cong_788 v0 v1 v2 ~v3 v4 v5 v6
  = du_i2f'45'cong_788 v0 v1 v2 v4 v5 v6
du_i2f'45'cong_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_i2f'45'cong_788 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v6
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_i2f'45'cong'738'_660
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.coerce-cong
d_coerce'45'cong_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_coerce'45'cong_818 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_coerce'45'cong_818 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_coerce'45'cong_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_coerce'45'cong_818 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v9
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_coerce'45'cong'738'_682
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.morph-app-cong
d_morph'45'app'45'cong_854 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_morph'45'app'45'cong_854 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v10
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_morph'45'app'45'cong'738'_706
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.app-cong
d_app'45'cong_896 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_app'45'cong_896 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v14
        -> case coe v13 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_app'45'cong'738'_742
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.effApp-cong
d_effApp'45'cong_948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_effApp'45'cong_948 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12 v13
                     v14
  = du_effApp'45'cong_948
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13 v14
du_effApp'45'cong_948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_effApp'45'cong_948 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v14
        -> case coe v13 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_effApp'45'cong'738'_804
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.comp-cong
d_comp'45'cong_1002 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_comp'45'cong_1002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14
  = case coe v13 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
        -> case coe v14 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v16
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_comp'45'cong'738'_842
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v15)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.copair-cong
d_copair'45'cong_1056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_copair'45'cong_1056 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14
  = case coe v13 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
        -> case coe v14 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v16
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_copair'45'cong'738'_880
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v15)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.fork-cong
d_fork'45'cong_1110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fork'45'cong_1110 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14
  = case coe v13 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
        -> case coe v14 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v16
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fork'45'cong'738'_922
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v15)
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.curry-cong
d_curry'45'cong_1160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_curry'45'cong_1160 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_curry'45'cong_1160 v0 v1 v2 v4 v5 v6 v8 v9 v10 v11
du_curry'45'cong_1160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_curry'45'cong_1160 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v10
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_curry'45'cong'738'_960
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.cata-cong
d_cata'45'cong_1202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_cata'45'cong_1202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_cata'45'cong'738'_990
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.ana-cong
d_ana'45'cong_1244 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_ana'45'cong_1244 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_ana'45'cong_1244 v0 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11
du_ana'45'cong_1244 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_ana'45'cong_1244 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v11
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_ana'45'cong'738'_1026
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.loop-cong
d_loop'45'cong_1274 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_loop'45'cong_1274 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v9
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_loop'45'cong'738'_1058
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.let-cong
d_let'45'cong_1314 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_let'45'cong_1314 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v14
        -> case coe v13 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v15
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_let'45'cong'738'_1100
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.case-cong
d_case'45'cong_1374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_case'45'cong_1374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v20
        -> case coe v18 of
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v21
               -> case coe v19 of
                    MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v22
                      -> coe
                           MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
                           (coe
                              MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_case'45'cong'738'_1162
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
                              (coe v14) (coe v15) (coe v16) (coe v20) (coe v21) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.lam-cong
d_lam'45'cong_1436 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_lam'45'cong_1436 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
                   v12
  = du_lam'45'cong_1436 v4 v8 v12
du_lam'45'cong_1436 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_lam'45'cong_1436 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82 v3
        -> coe
             MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
             (coe
                MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_lam'45'cong'738'_1204
                v0 v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoherenceLawsWrap._.coerce-refl
d_coerce'45'refl_1472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_coerce'45'refl_1472 v0 v1 v2 ~v3 v4 v5
  = du_coerce'45'refl_1472 v0 v1 v2 v4 v5
du_coerce'45'refl_1472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_coerce'45'refl_1472 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_coerce'45'refl'738'_1290
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.CoherenceLawsWrap._.coerce-trans
d_coerce'45'trans_1502 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_coerce'45'trans_1502 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_coerce'45'trans_1502 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_coerce'45'trans_1502 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_coerce'45'trans_1502 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_coerce'45'trans'738'_1316
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
-- Once.Adequacy.CoherenceLawsWrap._.coerce-uniq
d_coerce'45'uniq_1538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_coerce'45'uniq_1538 v0 v1 v2 ~v3 v4 v5 ~v6 v7 v8
  = du_coerce'45'uniq_1538 v0 v1 v2 v4 v5 v7 v8
du_coerce'45'uniq_1538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_coerce'45'uniq_1538 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_coerce'45'uniq'738'_1350
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Adequacy.CoherenceLawsWrap._.pair-coerce
d_pair'45'coerce_1580 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_pair'45'coerce_1580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_pair'45'coerce'738'_1388
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
-- Once.Adequacy.CoherenceLawsWrap._.app-coerce
d_app'45'coerce_1628 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_app'45'coerce_1628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_app'45'coerce'738'_1426
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.CoherenceLawsWrap._.comp-post
d_comp'45'post_1680 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_comp'45'post_1680 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_comp'45'post'738'_1472
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
         (coe v14))
-- Once.Adequacy.CoherenceLawsWrap._.comp-pre
d_comp'45'pre_1742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_comp'45'pre_1742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_comp'45'pre'738'_1530
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
         (coe v14) (coe v15) (coe v16))
-- Once.Adequacy.CoherenceLawsWrap._.lam-coerce
d_lam'45'coerce_1798 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_lam'45'coerce_1798 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_lam'45'coerce_1798 v0 v1 v2 v4 v6 v7 v8 v10 v11
du_lam'45'coerce_1798 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_lam'45'coerce_1798 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_lam'45'coerce'738'_1578
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
-- Once.Adequacy.CoherenceLawsWrap._.copair-coerce
d_copair'45'coerce_1848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_copair'45'coerce_1848 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_copair'45'coerce'738'_1648
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13))
-- Once.Adequacy.CoherenceLawsWrap._.fork-coerce
d_fork'45'coerce_1906 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_fork'45'coerce_1906 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_fork'45'coerce'738'_1704
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12) (coe v13)
         (coe v14) (coe v15))
-- Once.Adequacy.CoherenceLawsWrap._.initial-coerce
d_initial'45'coerce_1948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_initial'45'coerce_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_initial'45'coerce_1948
du_initial'45'coerce_1948 ::
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
du_initial'45'coerce_1948
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (\ v0 v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Once.Adequacy.CoherenceLaws.du_initial'45'coerce'738'_1740)
-- Once.Adequacy.CoherenceLawsWrap._.cata-coerce
d_cata'45'coerce_1984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Adequacy.CoherenceLaws.T__'8776'__64
d_cata'45'coerce_1984 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.CoherenceLaws.C_'8776''45'intro_82
      (coe
         MAlonzo.Code.Once.Adequacy.CoherenceLaws.d_cata'45'coerce'738'_2226
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
