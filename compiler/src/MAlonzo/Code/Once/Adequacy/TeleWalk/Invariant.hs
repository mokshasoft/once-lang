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

module MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CoreEnv
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.MeaningBridge
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.Adequacy.TeleEntry
import qualified MAlonzo.Code.Once.Adequacy.TeleEnvLemmas
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.Abstract
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Schema
import qualified MAlonzo.Code.Once.Spec.Core.Telescope
import qualified MAlonzo.Code.Once.Spec.Core.Translate
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Instance
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.TeleWalk.Invariant.ι
d_ι_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268
d_ι_14 ~v0 v1 v2 = du_ι_14 v1 v2
du_ι_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268
du_ι_14 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_278 (coe v0)
      (coe v1)
-- Once.Adequacy.TeleWalk.Invariant.φ
d_φ_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_φ_16 ~v0 v1 v2 = du_φ_16 v1 v2
du_φ_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
du_φ_16 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_350
      (coe du_ι_14 (coe v0) (coe v1))
-- Once.Adequacy.TeleWalk.Invariant._.RelGM
d_RelGM_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGM_20 = erased
-- Once.Adequacy.TeleWalk.Invariant._.RefsAgree
d_RefsAgree_24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_RefsAgree_24 = erased
-- Once.Adequacy.TeleWalk.Invariant._.spliceClosed
d_spliceClosed_38 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceClosed_38 ~v0 ~v1 ~v2 = du_spliceClosed_38
du_spliceClosed_38 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_spliceClosed_38
  = coe MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_spliceClosed_66
-- Once.Adequacy.TeleWalk.Invariant._.σW
d_σW_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σW_40 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant._.abiT
d_abiT_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_abiT_56 ~v0 ~v1 ~v2 = du_abiT_56
du_abiT_56 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_abiT_56 = coe MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158
-- Once.Adequacy.TeleWalk.Invariant.NoShadow
d_NoShadow_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_NoShadow_58 = erased
-- Once.Adequacy.TeleWalk.Invariant.Inv
d_Inv_84 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Inv_84
  = C_constructor_130 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_Type_108 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_Type_108 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748)
                      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                      ([MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.TeleWalk.Invariant.Inv.irf
d_irf_116 ::
  T_Inv_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irf_116 v0
  = case coe v0 of
      C_constructor_130 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.irs
d_irs_118 ::
  T_Inv_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irs_118 v0
  = case coe v0 of
      C_constructor_130 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.iself
d_iself_120 ::
  T_Inv_84 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_120 v0
  = case coe v0 of
      C_constructor_130 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.rel
d_rel_128 ::
  T_Inv_84 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel_128 v0
  = case coe v0 of
      C_constructor_130 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.bare-ne
d_bare'45'ne_142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_bare'45'ne_142 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_bare'45'ne_142 v4 v6
du_bare'45'ne_142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_bare'45'ne_142 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (\ v8 -> coe v6 erased) (coe du_bare'45'ne_142 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.ns-step
d_ns'45'step_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'step_172 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_ns'45'step_172 v3 v9 v10
du_ns'45'step_172 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'step_172 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v12
                           (coe du_ns'45'step_172 (coe v4) (coe v1) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.ns-head
d_ns'45'head_214 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'head_214 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_ns'45'head_214 v3 v7
du_ns'45'head_214 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'head_214 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10
                           (coe du_ns'45'head_214 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.inv-sig
d_inv'45'sig_254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_Inv_84 -> T_Inv_84
d_inv'45'sig_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 v14 ~v15 v16
  = du_inv'45'sig_254 v11 v14 v16
du_inv'45'sig_254 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  T_Inv_84 -> T_Inv_84
du_inv'45'sig_254 v0 v1 v2
  = coe
      C_constructor_130 (coe d_irf_116 (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v0)
         (coe v1) (coe d_irs_118 (coe v2)))
      (coe d_iself_120 (coe v2)) (coe d_rel_128 (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.splice-form
d_splice'45'form_290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splice'45'form_290 = erased
-- Once.Adequacy.TeleWalk.Invariant.impEnv-wk
d_impEnv'45'wk_318 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_impEnv'45'wk_318 = erased
-- Once.Adequacy.TeleWalk.Invariant.defEnv-wk
d_defEnv'45'wk_350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defEnv'45'wk_350 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.x
d_x_400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_x_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18
  = du_x_400 v12
du_x_400 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_x_400 v0 = coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.δ
d_δ_402 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ_402 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18
  = du_δ_402 v0 v1 v2 v3 v4 v6
du_δ_402 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ_402 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
      (coe v3) (coe v4) (coe v0) (coe v2) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.S′
d_S'8242'_404 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
d_S'8242'_404 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_S'8242'_404 v4 v13
du_S'8242'_404 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
du_S'8242'_404 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v0
      (MAlonzo.Code.Once.Spec.Core.Translate.d_monoSchema_8 (coe v1))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.bodyT
d_bodyT_406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
d_bodyT_406 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18
  = du_bodyT_406 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyT_406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
du_bodyT_406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_726
      (coe (0 :: Integer))
      (\ v10 -> coe MAlonzo.Code.Once.Spec.Core.Telescope.du_noKinds_96)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Spec.Core.Translate.d_monoElab_610 (coe v0)
            (coe v1) (coe v2)
            (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
            (coe v7) (coe v8)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v4)
            (coe v5) (coe v6) (coe v9)))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.bodyD
d_bodyD_408 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
d_bodyD_408 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18
  = du_bodyD_408 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_408 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
du_bodyD_408 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Translate.du_monoBody_628 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
      (coe v7) (coe v8)
      (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v4)
      (coe v5) (coe v6) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.tl′
d_tl'8242'_410 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
d_tl'8242'_410 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13
               ~v14 v15 ~v16 ~v17 ~v18
  = du_tl'8242'_410 v1 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_tl'8242'_410 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
du_tl'8242'_410 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.C_def_28 v4
      (coe
         du_bodyT_406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10))
      (coe
         du_bodyD_408 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.δ′
d_δ'8242'_412 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ'8242'_412 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              v15 ~v16 ~v17 ~v18
  = du_δ'8242'_412 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_δ'8242'_412 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ'8242'_412 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v3))
      (coe
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v4
         (MAlonzo.Code.Once.Spec.Core.Translate.d_monoSchema_8 (coe v11)))
      (coe v0) (coe v2)
      (coe
         du_tl'8242'_410 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.e
d_e_414 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18
  = du_e_414 v12 v13 v16
du_e_414 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_414 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_846
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
         (coe
            MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe du_x_400 (coe v0)))
         (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ctx
d_ctx_416 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctx_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_ctx_416 v5
du_ctx_416 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
du_ctx_416 v0
  = coe
      MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ρ
d_ρ_418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
d_ρ_418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
        ~v16 ~v17 ~v18
  = du_ρ_418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
du_ρ_418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_308 (coe v1)
      (coe
         du_δ_402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v5))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_400
         (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
      (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.V
d_V_420 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Spec.Elaboration.T_View_506
d_V_420 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18
  = du_V_420 v5 v7 v8 v9
du_V_420 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506
du_V_420 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Translate.du_viewOf_542
      (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_400
         (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.Dc
d_Dc_422 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_Dc_422 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18
  = du_Dc_422 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_422 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_Dc_422 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_782 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
            (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v3))
            (coe
               MAlonzo.Code.Once.Compile.d_buildPolyCtx_274
               (coe
                  MAlonzo.Code.Once.Compile.d_telePolys_400
                  (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v3))))
            (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v3)))
         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v7)) (coe v8)
         (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
         (coe du_V_420 (coe v3) (coe v4) (coe v5) (coe v6)) (coe v9))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.uf
d_uf_424 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
         ~v14 ~v15 ~v16 ~v17 ~v18
  = du_uf_424 v5 v12 v13
du_uf_424 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_424 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_x_400 (coe v1))
         (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.σx
d_σx_426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σx_426 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
         ~v15 ~v16 ~v17 ~v18
  = du_σx_426 v0 v1 v2 v5 v10 v12 v13
du_σx_426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σx_426 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe v4)
      (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v3))
      (coe
         MAlonzo.Code.Once.Compile.d_declImps_406
         (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v3)))
      (coe du_uf_424 (coe v3) (coe v5) (coe v6))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ccE
d_ccE_428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccE_428 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 v15 ~v16 ~v17 ~v18
  = du_ccE_428 v5 v12 v13 v15
du_ccE_428 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccE_428 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_2516
      (coe
         MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) (coe v2)
      (coe v3)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ce
d_ce_430 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_430 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.D′
d_D'8242'_432 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_432 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_D'8242'_432 v5 v12 v13
du_D'8242'_432 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_432 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_334
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
         (coe du_ctx_416 (coe v0))
         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.M
d_M_434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_M_434 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
        ~v15 v16 ~v17 ~v18
  = du_M_434 v0 v1 v2 v10 v13 v16
du_M_434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_M_434 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
         (coe du_φ_16 (coe v1) (coe v2)) (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe MAlonzo.Code.Once.Type.C_Unit_120))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4)) (coe v5)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.chain
d_chain_436 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain_436 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.relA
d_relA_440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_relA_440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           ~v16 ~v17 v18
  = du_relA_440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v18
du_relA_440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_relA_440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.MeaningBridge.d_bridge'45'c_1744
      (coe v0)
      (coe
         du_σx_426 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v11)
         (coe v12))
      (coe
         MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
      (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v13)
      (coe
         MAlonzo.Code.Once.Denotation.Meaning.C_meanings_366
         (coe
            MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_94
            (coe
               MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
               (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe (\ v15 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v15)))
               (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Denotation.Meaning.d_entries_348
            (coe
               MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_308 (coe v1)
               (coe
                  MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
                  (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406
                  (coe
                     MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402
                  (coe
                     MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Data.List.Base.du_map_22
                  (coe (\ v15 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v15)))
                  (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
               (coe v7) (coe v8) (coe v9)))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_278 (coe v1)
            (coe
               MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_364
               (coe
                  MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
                  (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))))
         (coe
            (\ v15 v16 v17 v18 ->
               MAlonzo.Code.Once.Spec.Elaboration.d_member_476
                 (coe
                    MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376
                    (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5)) (coe v7)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v16
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("." :: Data.Text.Text) v15)))))
         (coe
            (\ v15 v16 v17 ->
               MAlonzo.Code.Once.Spec.Elaboration.d_member_476
                 (coe
                    MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376
                    (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5)) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v15))))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.C_mk'8638'_152
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         d_rel_128 v14 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
         (MAlonzo.Code.Once.Compile.d_declImps_406
            (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
         (d_iself_120 (coe v14))
         (coe du_uf_424 (coe v5) (coe v11) (coe v12)))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.entry≡
d_entry'8801'_442 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8801'_442 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.relM
d_relM_444 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_relM_444 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           v16 ~v17 v18
  = du_relM_444 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_relM_444 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_relM_444 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEntry.du_abi'45'rel_104 (coe v12)
      (coe
         du_M_434 (coe v0) (coe v1) (coe v2) (coe v10) (coe v12) (coe v14))
      (coe
         du_relA_440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v15))
-- Once.Adequacy.TeleWalk.Invariant.inv-mono
d_inv'45'mono_480 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_84
d_inv'45'mono_480 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                  v14 v15
  = du_inv'45'mono_480
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v15
du_inv'45'mono_480 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_84
du_inv'45'mono_480 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = coe
      seq (coe v14)
      (coe
         (\ v15 v16 v17 v18 v19 ->
            coe
              C_constructor_130
              (coe
                 MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28
                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v11)) (coe v13)
                 (coe d_irf_116 (coe v18)))
              (coe d_irs_118 (coe v18)) (coe d_iself_120 (coe v18))
              (coe
                 du_rel'8242'_570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                 (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                 (coe v12) (coe v15) (coe v16) (coe v18) (coe v19))))
-- Once.Adequacy.TeleWalk.Invariant._._.Dc
d_Dc_520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_Dc_520 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18 ~v19
  = du_Dc_520 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_520 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_Dc_520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_Dc_422 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.D′
d_D'8242'_522 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_522 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_D'8242'_522 v5 v12 v13
du_D'8242'_522 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_522 v0 v1 v2
  = coe du_D'8242'_432 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.M
d_M_524 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_M_524 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19
  = du_M_524 v0 v1 v2 v10 v13 v16
du_M_524 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_M_524 v0 v1 v2 v3 v4 v5
  = coe
      du_M_434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.S′
d_S'8242'_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
d_S'8242'_526 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_S'8242'_526 v4 v13
du_S'8242'_526 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
du_S'8242'_526 v0 v1 = coe du_S'8242'_404 (coe v0) (coe v1)
-- Once.Adequacy.TeleWalk.Invariant._._.V
d_V_528 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506
d_V_528 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_V_528 v5 v7 v8 v9
du_V_528 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506
du_V_528 v0 v1 v2 v3
  = coe du_V_420 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyD
d_bodyD_530 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
d_bodyD_530 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyD_530 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_530 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
du_bodyD_530 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyD_408 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyT
d_bodyT_532 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
d_bodyT_532 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyT_532 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyT_532 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
du_bodyT_532 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyT_406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.ccE
d_ccE_534 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccE_534 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_ccE_534 v5 v12 v13 v15
du_ccE_534 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccE_534 v0 v1 v2 v3
  = coe du_ccE_428 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.ce
d_ce_536 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_536 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.chain
d_chain_538 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain_538 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.ctx
d_ctx_540 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctx_540 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ctx_540 v5
du_ctx_540 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
du_ctx_540 v0 = coe du_ctx_416 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.e
d_e_542 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_e_542 v12 v13 v16
du_e_542 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_542 v0 v1 v2 = coe du_e_414 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.entry≡
d_entry'8801'_544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8801'_544 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.relA
d_relA_546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_relA_546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           ~v16 ~v17 v18 ~v19
  = du_relA_546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v18
du_relA_546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_relA_546 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_relA_440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
-- Once.Adequacy.TeleWalk.Invariant._._.relM
d_relM_548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_relM_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           v16 ~v17 v18 ~v19
  = du_relM_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_relM_548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_relM_548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_relM_444 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15)
-- Once.Adequacy.TeleWalk.Invariant._._.tl′
d_tl'8242'_550 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
d_tl'8242'_550 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13
               ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_tl'8242'_550 v1 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_tl'8242'_550 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
du_tl'8242'_550 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_tl'8242'_410 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.uf
d_uf_552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_552 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_uf_552 v5 v12 v13
du_uf_552 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_552 v0 v1 v2 = coe du_uf_424 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.x
d_x_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_x_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_x_554 v12
du_x_554 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_x_554 v0 = coe du_x_400 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.δ
d_δ_556 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ_556 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18 ~v19
  = du_δ_556 v0 v1 v2 v3 v4 v6
du_δ_556 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ_556 v0 v1 v2 v3 v4 v5
  = coe
      du_δ_402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.δ′
d_δ'8242'_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ'8242'_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              v15 ~v16 ~v17 ~v18 ~v19
  = du_δ'8242'_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_δ'8242'_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ'8242'_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_δ'8242'_412 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
-- Once.Adequacy.TeleWalk.Invariant._._.ρ
d_ρ_560 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
d_ρ_560 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
        ~v16 ~v17 ~v18 ~v19
  = du_ρ_560 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_560 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
du_ρ_560 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_ρ_418 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.σx
d_σx_562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σx_562 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
         ~v15 ~v16 ~v17 ~v18 ~v19
  = du_σx_562 v0 v1 v2 v5 v10 v12 v13
du_σx_562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σx_562 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_σx_426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6)
-- Once.Adequacy.TeleWalk.Invariant._.rel′
d_rel'8242'_570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel'8242'_570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14
                v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_rel'8242'_570
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18 v19 v20 v21
      v22 v23 v24
du_rel'8242'_570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rel'8242'_570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_old_588 (coe v5) (coe v11) (coe v12) (coe v14) (coe v15)
            (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_new_596 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     du_old_588 (coe v5) (coe v11) (coe v12) (coe v14) (coe v15)
                     (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)))))
         erased)
-- Once.Adequacy.TeleWalk.Invariant._._.σ
d_σ_586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ_586 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19 v20 ~v21 v22 ~v23 v24
  = du_σ_586 v0 v1 v2 v5 v10 v12 v13 v16 v20 v22 v24
du_σ_586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ_586 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_414 (coe v5) (coe v6) (coe v7)) (coe v4)))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v3)) (coe v9)
      (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.old
d_old_588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_old_588 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 ~v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_old_588 v5 v12 v13 v16 v18 v19 v20 v21 v22 v23 v24
du_old_588 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_old_588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      d_rel_128 v4
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_414 (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         du_ns'45'step_172 (coe v6)
         (coe
            du_bare'45'ne_142
            (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0)) (coe v5))
         (coe v7))
      v8 v9 v10
-- Once.Adequacy.TeleWalk.Invariant._._.callEq
d_callEq_594 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_callEq_594 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.new
d_new_596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_new_596 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
          v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_new_596 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_new_596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_new_596 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_relM_444 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15)
-- Once.Adequacy.TeleWalk.Invariant.inv-poly
d_inv'45'poly_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_84
d_inv'45'poly_630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
  = du_inv'45'poly_630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inv'45'poly_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_84
du_inv'45'poly_630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         (\ v13 v14 v15 ->
            coe
              C_constructor_130 (coe d_irf_116 (coe v14))
              (coe d_irs_118 (coe v14))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                 (coe
                    MAlonzo.Code.Once.Adequacy.TelePosition.du_iself'45'step_138
                    (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5))
                    (coe du_frT_682 (coe v5) (coe v15)) (coe d_iself_120 (coe v14))))
              (coe
                 du_rel'8242'_690 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                 (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                 (coe v13) (coe v14) (coe v15))))
-- Once.Adequacy.TeleWalk.Invariant._.y
d_y_660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_y_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15
  = du_y_660 v12
du_y_660 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_y_660 v0 = coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._.scT
d_scT_662 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
d_scT_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15
  = du_scT_662 v12
du_scT_662 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
du_scT_662 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._.bodyT
d_bodyT_664 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
d_bodyT_664 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            ~v15
  = du_bodyT_664 v1 v3 v4 v5 v7 v8 v9 v12 v13
du_bodyT_664 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
du_bodyT_664 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_726
      (coe
         MAlonzo.Code.Once.Type.Rigid.d_arityOf_82
         (coe du_scT_662 (coe v7)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Schema.d_kindsOf_352
         (coe du_scT_662 (coe v7)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Spec.Core.Translate.d_polyElab_700 (coe v0)
            (coe v1) (coe v2)
            (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
            (coe v7) (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe v4) (coe v5) (coe v6) (coe v8)))
-- Once.Adequacy.TeleWalk.Invariant._.bodyD
d_bodyD_666 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
d_bodyD_666 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            ~v15
  = du_bodyD_666 v1 v3 v4 v5 v7 v8 v9 v12 v13
du_bodyD_666 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
du_bodyD_666 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.Translate.du_polyBody_720 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
      (coe v7) (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.Adequacy.TeleWalk.Invariant._.S′
d_S'8242'_668 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
d_S'8242'_668 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              ~v13 ~v14 ~v15
  = du_S'8242'_668 v4 v12
du_S'8242'_668 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
du_S'8242'_668 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v0
      (MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
         (coe du_scT_662 (coe v1)))
-- Once.Adequacy.TeleWalk.Invariant._.δ
d_δ_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ_670 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15
  = du_δ_670 v0 v1 v2 v3 v4 v6
du_δ_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ_670 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
      (coe v3) (coe v4) (coe v0) (coe v2) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._.δ′
d_δ'8242'_672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_δ'8242'_672 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              ~v15
  = du_δ'8242'_672 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13
du_δ'8242'_672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
du_δ'8242'_672 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v3))
      (coe
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v4
         (MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
            (coe du_scT_662 (coe v10))))
      (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Core.Telescope.C_def_28 v6
         (coe
            du_bodyT_664 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
            (coe v9) (coe v10) (coe v11))
         (coe
            du_bodyD_666 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
            (coe v9) (coe v10) (coe v11)))
-- Once.Adequacy.TeleWalk.Invariant._.ctx
d_ctx_674 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctx_674 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_ctx_674 v5
du_ctx_674 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
du_ctx_674 v0
  = coe
      MAlonzo.Code.Once.Spec.Module.d_ctxOf_24
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant._.ρ
d_ρ_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
d_ρ_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_ρ_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_318
du_ρ_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_308 (coe v1)
      (coe
         du_δ_670 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v5))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_400
         (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
      (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._.V
d_V_678 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506
d_V_678 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15
  = du_V_678 v5 v7 v8 v9
du_V_678 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506
du_V_678 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Translate.du_viewOf_542
      (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_400
         (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._.frT
d_frT_682 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frT_682 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15
  = du_frT_682 v5 v15
du_frT_682 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_frT_682 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_'43''43''8315''691'_170
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
         (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0)))
      (coe v1)
-- Once.Adequacy.TeleWalk.Invariant._.rel′
d_rel'8242'_690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel'8242'_690 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20
  = du_rel'8242'_690
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      v20
du_rel'8242'_690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rel'8242'_690 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = case coe v18 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v22 v23
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   du_head_738 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                   (coe v13) (coe v15) (coe v16) (coe v17) (coe v23) (coe v19))
                (coe
                   MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_envrel'45'transport_296
                   (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v5))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_94
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Telescope.d_teleSem_36 (coe v1)
                         (coe addInt (coe (1 :: Integer)) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v4
                            (MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
                               (coe du_scT_662 (coe v11))))
                         (coe v0) (coe v2)
                         (coe
                            MAlonzo.Code.Once.Spec.Core.Telescope.C_def_28 v6
                            (coe
                               du_bodyT_664 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
                               (coe v9) (coe v11) (coe v12))
                            (coe
                               du_bodyD_666 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
                               (coe v9) (coe v11) (coe v12))))
                      (coe
                         MAlonzo.Code.Once.Compile.d_telePolys_400
                         (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Spec.Core.Translate.du_wkT_156
                         (coe
                            MAlonzo.Code.Once.Compile.d_telePolys_400
                            (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
                         (coe v9)))
                   (coe
                      du_ra_722 (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5))
                      (coe du_frT_682 (coe v5) (coe v14)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         du_old_714 (coe v13) (coe v15) (coe v16) (coe v17) (coe v23)
                         (coe v19)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_imprel'45'transport_352
                   (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v5))
                   (coe
                      MAlonzo.Code.Once.Denotation.Meaning.d_entries_348
                      (coe
                         du_ρ_676 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8) (coe v9)))
                   (coe
                      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_calls'45'same_634
                      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v5)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            du_old_714 (coe v13) (coe v15) (coe v16) (coe v17) (coe v23)
                            (coe v19)))))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant._._.tbl
d_tbl_708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tbl_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tbl_708 v10 v16
du_tbl_708 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_tbl_708 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.σo
d_σo_710 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σo_710 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 v21
  = du_σo_710 v0 v1 v2 v5 v10 v16 v18 v21
du_σo_710 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σo_710 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe du_tbl_708 (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v3)) (coe v6)
      (coe v7)
-- Once.Adequacy.TeleWalk.Invariant._._.σ
d_σ_712 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ_712 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 ~v13 ~v14
        ~v15 v16 ~v17 v18 ~v19 ~v20 v21
  = du_σ_712 v0 v1 v2 v5 v10 v12 v16 v18 v21
du_σ_712 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ_712 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe du_tbl_708 (coe v4) (coe v6))
      (coe
         MAlonzo.Code.Once.Compile.d_cpolys_402
         (coe MAlonzo.Code.Once.Compile.d_addEntry_450 (coe v3) (coe v5)))
      (coe v7) (coe v8)
-- Once.Adequacy.TeleWalk.Invariant._._.old
d_old_714 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_old_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15 v16 v17 v18 ~v19 v20 v21
  = du_old_714 v14 v16 v17 v18 v20 v21
du_old_714 ::
  T_Inv_84 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_old_714 v0 v1 v2 v3 v4 v5 = coe d_rel_128 v0 v1 v2 v3 v4 v5
-- Once.Adequacy.TeleWalk.Invariant._._.ra
d_ra_722 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_ra_722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
  = du_ra_722 v22 v23
du_ra_722 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_ra_722 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_ra_722 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant._._.head
d_head_738 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_head_738 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 v14 ~v15
           v16 v17 v18 ~v19 v20 v21 v22 v23
  = du_head_738
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v16 v17 v18 v20 v21
      v22 v23
du_head_738 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_head_738 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.Adequacy.MeaningBridge.d_bridge'45'c_1744
      (coe v0)
      (coe
         du_σo_710 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v14)
         (coe v16) (coe v18))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_422
            (coe
               MAlonzo.Code.Once.Spec.Module.d_sig_14
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
            (coe
               MAlonzo.Code.Once.Spec.Module.d_imps_16
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_274
            (coe
               MAlonzo.Code.Once.Spec.Module.d_tele_18
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v11)) (coe v19)
      (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
      (coe
         du_D'45'U_748 (coe v5) (coe v11) (coe v12) (coe v13) (coe v20))
      (coe
         MAlonzo.Code.Once.Denotation.Meaning.C_meanings_366
         (coe
            MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_94
            (coe
               du_δ_670 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
            (coe
               MAlonzo.Code.Once.Compile.d_telePolys_400
               (MAlonzo.Code.Once.Compile.d_ctele_390 (coe v5)))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Denotation.Meaning.d_entries_348
            (coe
               du_ρ_676 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9)))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_278 (coe v1)
            (coe
               MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_364
               (coe
                  du_δ_670 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))))
         (coe
            (\ v21 v22 v23 v24 ->
               MAlonzo.Code.Once.Spec.Elaboration.d_member_476
                 (coe
                    MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376
                    (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5)) (coe v7)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v22
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("." :: Data.Text.Text) v21)))))
         (coe
            (\ v21 v22 v23 ->
               MAlonzo.Code.Once.Spec.Elaboration.d_member_476
                 (coe
                    MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376
                    (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v5)) (coe v7)
                    (coe
                       MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v21))))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.C_mk'8638'_152
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         du_old_714 (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
         (coe v18))
-- Once.Adequacy.TeleWalk.Invariant._._._.D-U
d_D'45'U_748 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'45'U_748 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
             v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_D'45'U_748 v5 v12 v13 v14 v23
du_D'45'U_748 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'45'U_748 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_24
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_422
         (coe
            MAlonzo.Code.Once.Spec.Module.d_sig_14
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
         (coe
            MAlonzo.Code.Once.Spec.Module.d_imps_16
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
      (coe
         MAlonzo.Code.Once.Compile.d_buildPolyCtx_274
         (coe
            MAlonzo.Code.Once.Spec.Module.d_tele_18
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
      (coe du_scT_662 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_irf_116 (coe v3)) (coe d_irs_118 (coe v3)))
      (coe v2) (coe v4)
-- Once.Adequacy.TeleWalk.Invariant._._._.ccU
d_ccU_750 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccU_750 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
  = du_ccU_750 v5 v12 v13 v14 v22 v23
du_ccU_750 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccU_750 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_2516
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_422
            (coe
               MAlonzo.Code.Once.Spec.Module.d_sig_14
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
            (coe
               MAlonzo.Code.Once.Spec.Module.d_imps_16
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_274
            (coe
               MAlonzo.Code.Once.Spec.Module.d_tele_18
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1)) (coe v4)
      (coe du_D'45'U_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Adequacy.TeleWalk.Invariant._._._.ce
d_ce_752 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_752 = erased
-- Once.Adequacy.TeleWalk.Invariant._._._.cr
d_cr_754 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cr_754 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_cr_754 v5 v12 v22
du_cr_754 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cr_754 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
         (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v0))
         (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v0)))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1)) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._._.D′
d_D'8242'_756 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_756 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_D'8242'_756 v5 v12 v22
du_D'8242'_756 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_756 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_334
      (coe du_cr_754 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant._._._.eqSD
d_eqSD_758 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_84 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqSD_758 = erased
-- Once.Adequacy.TeleWalk.Invariant.mainIn-name
d_mainIn'45'name_780 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_mainIn'45'name_780 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mainIn'45'name_780 v4 v5 v6
du_mainIn'45'name_780 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_mainIn'45'name_780 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Module.C_ffi_64 v5 v9 v10 v11 v12
        -> case coe v0 of
             (:) v13 v14
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_mainIn'45'name_780 (coe v14) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_mono_76 v5 v7 v10 v11 v12
        -> case coe v0 of
             (:) v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                      -> coe
                           seq (coe v15)
                           (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                           (coe du_mainIn'45'name_780 (coe v14) (coe v12) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_poly_86 v6 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_mainIn'45'name_780 (coe v10) (coe v8) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.not-in
d_not'45'in_806 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45'in_806 = erased
-- Once.Adequacy.TeleWalk.Invariant.NS
d_NS_816 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> ()
d_NS_816 = erased
-- Once.Adequacy.TeleWalk.Invariant.ns-of
d_ns'45'of_832 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'of_832 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_ns'45'of_832 v4 v5
du_ns'45'of_832 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'of_832 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (\ v8 -> coe v6 erased) (coe du_ns'45'of_832 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.names-imps
d_names'45'imps_862 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_names'45'imps_862 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_names'45'imps_862 v4 v6
du_names'45'imps_862 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_names'45'imps_862 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6
                    (coe du_names'45'imps_862 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.later-ns
d_later'45'ns_892 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_later'45'ns_892 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_later'45'ns_892 v4 v5 v6 v7 v9
du_later'45'ns_892 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_later'45'ns_892 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bnil_16 -> coe v4
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v7 v9 v10 v11 v17
        -> case coe v0 of
             (:) v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v22 v23
                      -> coe
                           du_later'45'ns_892 (coe v19) (coe v17) (coe v2) (coe v23) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_64 v8 v9 v10 v11 v12 v13 v16 v20
        -> case coe v0 of
             (:) v21 v22
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v25 v26
                      -> coe
                           du_later'45'ns_892 (coe v22) (coe v20) (coe v2) (coe v26)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_ns'45'of_832 (coe v2) (coe v25)) v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_82 v8 v9 v10 v11 v13
        -> case coe v0 of
             (:) v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v18 v19
                      -> coe
                           du_later'45'ns_892 (coe v15) (coe v13) (coe v2) (coe v19) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.later-noshadow
d_later'45'noshadow_948 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_Entry_132 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_later'45'noshadow_948 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8
  = du_later'45'noshadow_948 v3 v6 v7 v8
du_later'45'noshadow_948 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_later'45'noshadow_948 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v8 v9
               -> coe
                    du_later'45'ns_892 (coe v1) (coe v2)
                    (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                       (coe
                          (\ v10 ->
                             coe
                               du_names'45'imps_862
                               (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_64)
                          (coe v1))
                       (coe v9))
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
