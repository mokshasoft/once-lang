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
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.Coherence
import qualified MAlonzo.Code.Once.Adequacy.CoreEnv
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Adequacy.MeaningBridge
import qualified MAlonzo.Code.Once.Adequacy.ResolveFaithful
import qualified MAlonzo.Code.Once.Adequacy.SourceFaithful
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.Adequacy.TeleEntry
import qualified MAlonzo.Code.Once.Adequacy.TeleEnvLemmas
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRelPER
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.Abstract
import qualified MAlonzo.Code.Once.Lang.Core.Meaning
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.Core.Schema
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Core.Translate
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Elaboration
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Instance

-- Once.Adequacy.TeleWalk.Invariant.ι
d_ι_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι_14 ~v0 v1 v2 = du_ι_14 v1 v2
du_ι_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι_14 v0 v1
  = coe MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v0) (coe v1)
-- Once.Adequacy.TeleWalk.Invariant.φ
d_φ_16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
d_φ_16 ~v0 v1 v2 = du_φ_16 v1 v2
du_φ_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
du_φ_16 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262
      (coe du_ι_14 (coe v0) (coe v1))
-- Once.Adequacy.TeleWalk.Invariant._.RelGM
d_RelGM_22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 -> ()
d_RelGM_22 = erased
-- Once.Adequacy.TeleWalk.Invariant._.RefsAgree
d_RefsAgree_26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_RefsAgree_26 = erased
-- Once.Adequacy.TeleWalk.Invariant._.spliceClosed
d_spliceClosed_40 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceClosed_40 ~v0 ~v1 ~v2 = du_spliceClosed_40
du_spliceClosed_40 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_spliceClosed_40
  = coe MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_spliceClosed_66
-- Once.Adequacy.TeleWalk.Invariant._.σW
d_σW_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σW_42 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant._.abiT
d_abiT_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_abiT_60 ~v0 ~v1 ~v2 = du_abiT_60
du_abiT_60 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_abiT_60 = coe MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158
-- Once.Adequacy.TeleWalk.Invariant.≡ˡ
d_'8801''737'_74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''737'_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8801''737'_74 v10
du_'8801''737'_74 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''737'_74 v0 = coe v0
-- Once.Adequacy.TeleWalk.Invariant.≡ʳ
d_'8801''691'_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''691'_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8801''691'_90 v10
du_'8801''691'_90 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''691'_90 v0 = coe v0
-- Once.Adequacy.TeleWalk.Invariant.NoShadow
d_NoShadow_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_NoShadow_94 = erased
-- Once.Adequacy.TeleWalk.Invariant.Inv
d_Inv_120 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Inv_120
  = C_constructor_166 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68)
                      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                      ([MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.TeleWalk.Invariant.Inv.irf
d_irf_152 ::
  T_Inv_120 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irf_152 v0
  = case coe v0 of
      C_constructor_166 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.irs
d_irs_154 ::
  T_Inv_120 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irs_154 v0
  = case coe v0 of
      C_constructor_166 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.iself
d_iself_156 ::
  T_Inv_120 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_156 v0
  = case coe v0 of
      C_constructor_166 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.Inv.rel
d_rel_164 ::
  T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel_164 v0
  = case coe v0 of
      C_constructor_166 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.bare-ne
d_bare'45'ne_178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_bare'45'ne_178 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_bare'45'ne_178 v4 v6
du_bare'45'ne_178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_bare'45'ne_178 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (\ v8 -> coe v6 erased) (coe du_bare'45'ne_178 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.ns-step
d_ns'45'step_208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'step_208 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_ns'45'step_208 v3 v9 v10
du_ns'45'step_208 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'step_208 v0 v1 v2
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
                           (coe du_ns'45'step_208 (coe v4) (coe v1) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.ns-snoc
d_ns'45'snoc_250 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'snoc_250 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_ns'45'snoc_250 v3 v8 v9
du_ns'45'snoc_250 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'snoc_250 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7
                    (coe du_ns'45'snoc_250 (coe v4) (coe v1) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.ns-head
d_ns'45'head_290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'head_290 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_ns'45'head_290 v3 v7
du_ns'45'head_290 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'head_290 v0 v1
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
                           (coe du_ns'45'head_290 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.inv-sig
d_inv'45'sig_330 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_Inv_120 -> T_Inv_120
d_inv'45'sig_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 v14 ~v15 v16
  = du_inv'45'sig_330 v11 v14 v16
du_inv'45'sig_330 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  T_Inv_120 -> T_Inv_120
du_inv'45'sig_330 v0 v1 v2
  = coe
      C_constructor_166 (coe d_irf_152 (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v0)
         (coe v1) (coe d_irs_154 (coe v2)))
      (coe d_iself_156 (coe v2)) (coe d_rel_164 (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.splice-form
d_splice'45'form_366 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splice'45'form_366 = erased
-- Once.Adequacy.TeleWalk.Invariant.impEnv-wk
d_impEnv'45'wk_394 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_impEnv'45'wk_394 = erased
-- Once.Adequacy.TeleWalk.Invariant.defEnv-wk
d_defEnv'45'wk_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defEnv'45'wk_426 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.x
d_x_476 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_x_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18
  = du_x_476 v12
du_x_476 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_x_476 v0 = coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.δ
d_δ_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_478 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18
  = du_δ_478 v0 v1 v2 v3 v4 v6
du_δ_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ_478 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
      (coe v3) (coe v4) (coe v0) (coe v2) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.S′
d_S'8242'_480 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
d_S'8242'_480 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_S'8242'_480 v4 v13
du_S'8242'_480 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
du_S'8242'_480 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v0
      (MAlonzo.Code.Once.Lang.Core.Translate.d_monoSchema_8 (coe v1))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.bodyT
d_bodyT_482 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
d_bodyT_482 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18
  = du_bodyT_482 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyT_482 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
du_bodyT_482 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
      (coe (0 :: Integer))
      (\ v10 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Lang.Core.Translate.d_monoElab_630 (coe v0)
            (coe v1) (coe v2)
            (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
            (coe v7) (coe v8)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
            (coe v5) (coe v6) (coe v9)))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.bodyD
d_bodyD_484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_484 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18
  = du_bodyD_484 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_484 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_484 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.Translate.du_monoBody_648 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
      (coe v7) (coe v8)
      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
      (coe v5) (coe v6) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.tl′
d_tl'8242'_486 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
d_tl'8242'_486 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13
               ~v14 v15 ~v16 ~v17 ~v18
  = du_tl'8242'_486 v1 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_tl'8242'_486 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
du_tl'8242'_486 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v4
      (coe
         du_bodyT_482 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10))
      (coe
         du_bodyD_484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.δ′
d_δ'8242'_488 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ'8242'_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              v15 ~v16 ~v17 ~v18
  = du_δ'8242'_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_δ'8242'_488 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ'8242'_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v3))
      (coe
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v4
         (MAlonzo.Code.Once.Lang.Core.Translate.d_monoSchema_8 (coe v11)))
      (coe v0) (coe v2)
      (coe
         du_tl'8242'_486 (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.e
d_e_490 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18
  = du_e_490 v12 v13 v16
du_e_490 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_490 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_1042
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
         (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe du_x_476 (coe v0)))
         (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ctx
d_ctx_492 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_492 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_ctx_492 v5
du_ctx_492 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_492 v0
  = coe
      MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ρ
d_ρ_494 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
d_ρ_494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
        ~v16 ~v17 ~v18
  = du_ρ_494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_494 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
du_ρ_494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_306 (coe v1)
      (coe
         du_δ_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_418
         (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
      (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.V
d_V_496 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Elaboration.T_View_516
d_V_496 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18
  = du_V_496 v5 v7 v8 v9
du_V_496 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
du_V_496 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Translate.du_viewOf_562
      (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_418
         (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.Dc
d_Dc_498 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_Dc_498 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18
  = du_Dc_498 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_498 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_Dc_498 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
            (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v3))
            (coe
               MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
               (coe
                  MAlonzo.Code.Once.Compile.d_telePolys_418
                  (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3))))
            (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v3)))
         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v7)) (coe v8)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (coe du_V_496 (coe v3) (coe v4) (coe v5) (coe v6)) (coe v9))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.uf
d_uf_500 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_500 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
         ~v14 ~v15 ~v16 ~v17 ~v18
  = du_uf_500 v5 v12 v13
du_uf_500 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_500 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_x_476 (coe v1))
         (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.σx
d_σx_502 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σx_502 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
         ~v15 ~v16 ~v17 ~v18
  = du_σx_502 v0 v1 v2 v5 v10 v12 v13
du_σx_502 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σx_502 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe v4)
      (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
      (coe
         MAlonzo.Code.Once.Compile.d_declImps_424
         (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3)))
      (coe du_uf_500 (coe v3) (coe v5) (coe v6))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ccE
d_ccE_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccE_504 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 v15 ~v16 ~v17 ~v18
  = du_ccE_504 v5 v12 v13 v15
du_ccE_504 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccE_504 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_2644
      (coe
         MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) (coe v2)
      (coe v3)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.ce
d_ce_506 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_506 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.D′
d_D'8242'_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_508 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_D'8242'_508 v5 v12 v13
du_D'8242'_508 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_508 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_388
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6334
         (coe du_ctx_492 (coe v0))
         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.M
d_M_510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_M_510 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
        ~v15 v16 ~v17 ~v18
  = du_M_510 v0 v1 v2 v10 v13 v16
du_M_510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_M_510 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
         (coe du_φ_16 (coe v1) (coe v2)) (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4)) (coe v5)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.chain
d_chain_512 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_chain_512 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13
            ~v14 v15 ~v16 ~v17 ~v18
  = du_chain_512 v0 v1 v2 v5 v10 v12 v13 v15
du_chain_512 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_chain_512 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRelPER.du_RelS'45'trans_86
      (coe
         MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'trans_522
         (coe v6))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
            (coe du_φ_16 (coe v1) (coe v2)) (coe v4))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                  (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))))
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                  (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))))
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v6)
            (coe
               MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
               (coe v6) (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
               (coe
                  MAlonzo.Code.Once.Compile.d_declImps_424
                  (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_x_476 (coe v5))
                     (coe v6))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))))
               (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                     (coe
                        MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                           (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
                           (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))))
                     (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                     (coe
                        MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                           (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
                           (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                        (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3)))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                        (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))))
                  (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                  (coe
                     MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_388
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6334
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                           (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
                           (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)))
                        (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6))))))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe du_ctx_492 (coe v3)))
         (coe v6)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe du_ctx_492 (coe v3)))
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_imps_16
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3)))
               (coe
                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_tele_18
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_sig_14
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
            (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_D'8242'_508 (coe v3) (coe v5) (coe v6)))
         (coe v0)
         (coe
            MAlonzo.Code.Once.Adequacy.ResolveFaithful.d_σR_12 (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe du_φ_16 (coe v1) (coe v2)) (coe v4))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
            (coe
               MAlonzo.Code.Once.Compile.d_declImps_424
               (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3)))
            (coe du_uf_500 (coe v3) (coe v5) (coe v6)) (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v6)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_imps_16
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3)))
               (coe
                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_tele_18
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_sig_14
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
            (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v7))
         (coe v0)
         (coe
            du_σx_502 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.SourceFaithful.d_faithful'8709'_2530
         (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
            (coe du_φ_16 (coe v1) (coe v2)) (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.EvalRel.d_table'45'self_656 (coe v0)
            (coe du_φ_16 (coe v1) (coe v2)) (coe v4))
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v6)
         (coe
            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
            (coe v6) (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
            (coe
               MAlonzo.Code.Once.Compile.d_declImps_424
               (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3)))
            (coe du_uf_500 (coe v3) (coe v5) (coe v6)) (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_imps_16
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3)))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe
                        MAlonzo.Code.Once.Lang.Module.d_tele_18
                        (coe
                           MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_sig_14
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_D'8242'_508 (coe v3) (coe v5) (coe v6)))))
      (coe
         MAlonzo.Code.Once.Adequacy.Coherence.d_realize'45'invariant_1130
         (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
               (coe du_ctx_492 (coe v3)))
            (coe
               MAlonzo.Code.Once.Lang.Module.d_imps_16
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3)))
            (coe
               MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_tele_18
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
            (coe
               MAlonzo.Code.Once.Lang.Module.d_sig_14
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))))
         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v5)) (coe v6)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (coe du_D'8242'_508 (coe v3) (coe v5) (coe v6)) (coe v7)
         (coe
            du_σx_502 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6))
         (coe
            MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW'45'self_706 (coe v0)
            (coe du_φ_16 (coe v1) (coe v2)) (coe v4)
            (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
            (coe
               MAlonzo.Code.Once.Compile.d_declImps_424
               (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v3)))
            (coe du_uf_500 (coe v3) (coe v5) (coe v6)))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.relA
d_relA_516 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relA_516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           ~v16 ~v17 v18
  = du_relA_516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v18
du_relA_516 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relA_516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.MeaningBridge.d_bridge'45'c_2122
      (coe v0)
      (coe
         du_σx_502 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v11)
         (coe v12))
      (coe
         MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW'45'self_706 (coe v0)
         (coe du_φ_16 (coe v1) (coe v2)) (coe v10)
         (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v5))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_424
            (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
         (coe du_uf_500 (coe v5) (coe v11) (coe v12)))
      (coe
         MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v13)
      (coe
         MAlonzo.Code.Once.Denotation.Meaning.C_meanings_326
         (coe
            MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_92
            (coe
               MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
               (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe (\ v15 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v15)))
               (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
            (coe v9))
         (coe
            MAlonzo.Code.Once.Denotation.Meaning.d_entries_316
            (coe
               MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_306 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
                  (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Data.List.Base.du_map_22
                  (coe (\ v15 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v15)))
                  (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
               (coe v7) (coe v8) (coe v9)))
         (coe
            MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Core.Meaning.d_impl_376
               (coe
                  MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
                  (coe v3) (coe v4) (coe v0) (coe v2) (coe v6))))
         (coe
            (\ v15 v16 v17 ->
               MAlonzo.Code.Once.Lang.Elaboration.d_member_486
                 (coe
                    MAlonzo.Code.Once.Lang.Core.Translate.du_sigAt_396
                    (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)) (coe v7)
                    (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v15))))))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.C_mk'8638'_184
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         d_rel_164 v14 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
         (MAlonzo.Code.Once.Compile.d_declImps_424
            (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
         (d_iself_156 (coe v14))
         (coe du_uf_500 (coe v5) (coe v11) (coe v12)))
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.entry≡
d_entry'8801'_518 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8801'_518 = erased
-- Once.Adequacy.TeleWalk.Invariant.MonoStep.relM
d_relM_520 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relM_520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           v16 ~v17 v18
  = du_relM_520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_relM_520 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relM_520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEntry.du_abi'45'rel_138 (coe v12)
      (coe
         du_M_510 (coe v0) (coe v1) (coe v2) (coe v10) (coe v12) (coe v14))
      (coe
         MAlonzo.Code.Once.Adequacy.GradedRelation.d_GM'45'D_1246 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v12)
         (coe
            MAlonzo.Code.Once.Lang.Core.Meaning.du_'10214'_'10215'_502 v1
            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v1)
                  (coe v3) (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                     (coe (0 :: Integer))
                     (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                     (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                     (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
                     (coe
                        MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                        (coe
                           MAlonzo.Code.Once.Compile.d_telePolys_418
                           (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5))))
                     (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)))
                  (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                  (coe du_V_496 (coe v5) (coe v7) (coe v8) (coe v9)) (coe v13)))
            v12 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v1)
                  (coe v3) (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                     (coe (0 :: Integer))
                     (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                     (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                     (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
                     (coe
                        MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                        (coe
                           MAlonzo.Code.Once.Compile.d_telePolys_418
                           (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5))))
                     (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)))
                  (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                  (coe du_V_496 (coe v5) (coe v7) (coe v8) (coe v9)) (coe v13)))
            v0
            (coe
               du_δ_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v12)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_imps_16
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe
                        MAlonzo.Code.Once.Lang.Module.d_tele_18
                        (coe
                           MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_sig_14
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v13))
            (coe v0)
            (coe
               du_σx_502 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v11)
               (coe v12))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            du_M_510 (coe v0) (coe v1) (coe v2) (coe v10) (coe v12) (coe v14))
         (coe
            du_relA_516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
            (coe v13) (coe v15))
         (coe
            du_chain_512 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10)
            (coe v11) (coe v12) (coe v13)))
-- Once.Adequacy.TeleWalk.Invariant.inv-mono-at
d_inv'45'mono'45'at_558 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Bool ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
d_inv'45'mono'45'at_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12
                        v13 v14 v15 v16
  = du_inv'45'mono'45'at_558
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15 v16
du_inv'45'mono'45'at_558 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Bool ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
du_inv'45'mono'45'at_558 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13 v14 v15
  = if coe v3
      then coe
             seq (coe v15)
             (coe
                (\ v16 v17 v18 v19 v20 ->
                   coe
                     C_constructor_166 (coe d_irf_152 (coe v19))
                     (coe d_irs_154 (coe v19)) (coe d_iself_156 (coe v19))
                     (coe
                        du_rel'8242'_716 (coe v6) (coe v12) (coe v13) (coe v17) (coe v19)
                        (coe v20))))
      else coe
             seq (coe v15)
             (coe
                (\ v16 v17 v18 v19 v20 ->
                   coe
                     C_constructor_166
                     (coe
                        MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28
                        (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v12)) (coe v14)
                        (coe d_irf_152 (coe v19)))
                     (coe d_irs_154 (coe v19)) (coe d_iself_156 (coe v19))
                     (coe
                        du_rel'8242'_832 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                        (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                        (coe v13) (coe v16) (coe v17) (coe v19) (coe v20))))
-- Once.Adequacy.TeleWalk.Invariant.inv-mono
d_inv'45'mono_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
d_inv'45'mono_592 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                  v14 v15 v16 v17 ~v18 v19 v20
  = du_inv'45'mono_592
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v19 v20
du_inv'45'mono_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
du_inv'45'mono_592 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18
  = coe
      du_inv'45'mono'45'at_558 v0 v1 v2
      (MAlonzo.Code.Data.String.Properties.d__'61''61'__86
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v11))
         (coe ("main" :: Data.Text.Text)))
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 erased v17 v18
-- Once.Adequacy.TeleWalk.Invariant._._.Dc
d_Dc_666 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_Dc_666 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18 ~v19
  = du_Dc_666 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_666 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_Dc_666 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_Dc_498 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.D′
d_D'8242'_668 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_668 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_D'8242'_668 v5 v12 v13
du_D'8242'_668 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_668 v0 v1 v2
  = coe du_D'8242'_508 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.M
d_M_670 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_M_670 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19
  = du_M_670 v0 v1 v2 v10 v13 v16
du_M_670 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_M_670 v0 v1 v2 v3 v4 v5
  = coe
      du_M_510 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.S′
d_S'8242'_672 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
d_S'8242'_672 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_S'8242'_672 v4 v13
du_S'8242'_672 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
du_S'8242'_672 v0 v1 = coe du_S'8242'_480 (coe v0) (coe v1)
-- Once.Adequacy.TeleWalk.Invariant._._.V
d_V_674 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
d_V_674 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_V_674 v5 v7 v8 v9
du_V_674 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
du_V_674 v0 v1 v2 v3
  = coe du_V_496 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyD
d_bodyD_676 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_676 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyD_676 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_676 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyD_484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyT
d_bodyT_678 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
d_bodyT_678 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyT_678 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyT_678 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
du_bodyT_678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyT_482 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.ccE
d_ccE_680 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccE_680 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_ccE_680 v5 v12 v13 v15
du_ccE_680 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccE_680 v0 v1 v2 v3
  = coe du_ccE_504 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.ce
d_ce_682 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_682 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.chain
d_chain_684 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_chain_684 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_chain_684 v0 v1 v2 v5 v10 v12 v13 v15
du_chain_684 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_chain_684 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_chain_512 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7)
-- Once.Adequacy.TeleWalk.Invariant._._.ctx
d_ctx_686 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ctx_686 v5
du_ctx_686 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_686 v0 = coe du_ctx_492 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.e
d_e_688 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_e_688 v12 v13 v16
du_e_688 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_688 v0 v1 v2 = coe du_e_490 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.entry≡
d_entry'8801'_690 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8801'_690 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.relA
d_relA_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relA_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           ~v16 ~v17 v18 ~v19
  = du_relA_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v18
du_relA_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relA_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_relA_516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
-- Once.Adequacy.TeleWalk.Invariant._._.relM
d_relM_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relM_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           v16 ~v17 v18 ~v19
  = du_relM_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_relM_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relM_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_relM_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15)
-- Once.Adequacy.TeleWalk.Invariant._._.tl′
d_tl'8242'_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
d_tl'8242'_696 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13
               ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_tl'8242'_696 v1 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_tl'8242'_696 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
du_tl'8242'_696 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_tl'8242'_486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.uf
d_uf_698 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_698 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_uf_698 v5 v12 v13
du_uf_698 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_698 v0 v1 v2 = coe du_uf_500 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.x
d_x_700 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_x_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_x_700 v12
du_x_700 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_x_700 v0 = coe du_x_476 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.δ
d_δ_702 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_702 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18 ~v19
  = du_δ_702 v0 v1 v2 v3 v4 v6
du_δ_702 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ_702 v0 v1 v2 v3 v4 v5
  = coe
      du_δ_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.δ′
d_δ'8242'_704 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ'8242'_704 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              v15 ~v16 ~v17 ~v18 ~v19
  = du_δ'8242'_704 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_δ'8242'_704 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ'8242'_704 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_δ'8242'_488 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
-- Once.Adequacy.TeleWalk.Invariant._._.ρ
d_ρ_706 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
d_ρ_706 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
        ~v16 ~v17 ~v18 ~v19
  = du_ρ_706 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_706 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
du_ρ_706 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_ρ_494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.σx
d_σx_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σx_708 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
         ~v15 ~v16 ~v17 ~v18 ~v19
  = du_σx_708 v0 v1 v2 v5 v10 v12 v13
du_σx_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σx_708 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_σx_502 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6)
-- Once.Adequacy.TeleWalk.Invariant._.rel′
d_rel'8242'_716 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel'8242'_716 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 v13 ~v14 ~v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_rel'8242'_716 v5 v12 v13 v16 v18 v19 v20 v21 v22 v23 v24
du_rel'8242'_716 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rel'8242'_716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_old_734 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_old_734 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
         erased)
-- Once.Adequacy.TeleWalk.Invariant._._.σ
d_σ_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ_732 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19 v20 ~v21 v22 ~v23 v24
  = du_σ_732 v0 v1 v2 v5 v10 v12 v13 v16 v20 v22 v24
du_σ_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ_732 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_490 (coe v5) (coe v6) (coe v7)) (coe v4)))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)) (coe v9)
      (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.old
d_old_734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_old_734 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 ~v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_old_734 v5 v12 v13 v16 v18 v19 v20 v21 v22 v23 v24
du_old_734 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_old_734 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      d_rel_164 v4
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_490 (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         du_ns'45'snoc_250 (coe v6)
         (coe
            du_bare'45'ne_178
            (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0)) (coe v5))
         (coe v7))
      v8 v9 v10
-- Once.Adequacy.TeleWalk.Invariant._._.Dc
d_Dc_782 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_Dc_782 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
         v15 ~v16 ~v17 ~v18 ~v19
  = du_Dc_782 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_Dc_782 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_Dc_782 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_Dc_498 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.D′
d_D'8242'_784 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_784 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_D'8242'_784 v5 v12 v13
du_D'8242'_784 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_784 v0 v1 v2
  = coe du_D'8242'_508 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.M
d_M_786 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_M_786 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19
  = du_M_786 v0 v1 v2 v10 v13 v16
du_M_786 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_M_786 v0 v1 v2 v3 v4 v5
  = coe
      du_M_510 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.S′
d_S'8242'_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
d_S'8242'_788 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_S'8242'_788 v4 v13
du_S'8242'_788 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
du_S'8242'_788 v0 v1 = coe du_S'8242'_480 (coe v0) (coe v1)
-- Once.Adequacy.TeleWalk.Invariant._._.V
d_V_790 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
d_V_790 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_V_790 v5 v7 v8 v9
du_V_790 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
du_V_790 v0 v1 v2 v3
  = coe du_V_496 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyD
d_bodyD_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_792 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyD_792 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyD_792 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_792 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyD_484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.bodyT
d_bodyT_794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
d_bodyT_794 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_bodyT_794 v1 v3 v4 v5 v7 v8 v9 v12 v13 v15
du_bodyT_794 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
du_bodyT_794 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_bodyT_482 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.ccE
d_ccE_796 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccE_796 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_ccE_796 v5 v12 v13 v15
du_ccE_796 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccE_796 v0 v1 v2 v3
  = coe du_ccE_504 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._._.ce
d_ce_798 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_798 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.chain
d_chain_800 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_chain_800 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_chain_800 v0 v1 v2 v5 v10 v12 v13 v15
du_chain_800 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_chain_800 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_chain_512 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7)
-- Once.Adequacy.TeleWalk.Invariant._._.ctx
d_ctx_802 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_802 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_ctx_802 v5
du_ctx_802 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_802 v0 = coe du_ctx_492 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.e
d_e_804 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_e_804 v12 v13 v16
du_e_804 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_804 v0 v1 v2 = coe du_e_490 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.entry≡
d_entry'8801'_806 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8801'_806 = erased
-- Once.Adequacy.TeleWalk.Invariant._._.relA
d_relA_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relA_808 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           ~v16 ~v17 v18 ~v19
  = du_relA_808 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v18
du_relA_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relA_808 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_relA_516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14)
-- Once.Adequacy.TeleWalk.Invariant._._.relM
d_relM_810 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relM_810 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
           v16 ~v17 v18 ~v19
  = du_relM_810 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18
du_relM_810 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relM_810 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_relM_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15)
-- Once.Adequacy.TeleWalk.Invariant._._.tl′
d_tl'8242'_812 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
d_tl'8242'_812 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13
               ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_tl'8242'_812 v1 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_tl'8242'_812 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
du_tl'8242'_812 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_tl'8242'_486 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.uf
d_uf_814 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_814 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_uf_814 v5 v12 v13
du_uf_814 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_814 v0 v1 v2 = coe du_uf_500 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._.x
d_x_816 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_x_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_x_816 v12
du_x_816 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_x_816 v0 = coe du_x_476 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.δ
d_δ_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_818 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15 ~v16 ~v17 ~v18 ~v19
  = du_δ_818 v0 v1 v2 v3 v4 v6
du_δ_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ_818 v0 v1 v2 v3 v4 v5
  = coe
      du_δ_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._._.δ′
d_δ'8242'_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ'8242'_820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              v15 ~v16 ~v17 ~v18 ~v19
  = du_δ'8242'_820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13 v15
du_δ'8242'_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ'8242'_820 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_δ'8242'_488 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12)
-- Once.Adequacy.TeleWalk.Invariant._._.ρ
d_ρ_822 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
d_ρ_822 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
        ~v16 ~v17 ~v18 ~v19
  = du_ρ_822 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_822 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
du_ρ_822 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_ρ_494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._._.σx
d_σx_824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σx_824 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
         ~v15 ~v16 ~v17 ~v18 ~v19
  = du_σx_824 v0 v1 v2 v5 v10 v12 v13
du_σx_824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σx_824 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_σx_502 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6)
-- Once.Adequacy.TeleWalk.Invariant._.rel′
d_rel'8242'_832 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel'8242'_832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14
                v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_rel'8242'_832
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18 v19 v20 v21
      v22 v23 v24
du_rel'8242'_832 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rel'8242'_832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_old_850 (coe v5) (coe v11) (coe v12) (coe v14) (coe v15)
            (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_new_858 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v17) (coe v19) (coe v21))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     du_old_850 (coe v5) (coe v11) (coe v12) (coe v14) (coe v15)
                     (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)))))
         erased)
-- Once.Adequacy.TeleWalk.Invariant._._.σ
d_σ_848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ_848 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14
        ~v15 v16 ~v17 ~v18 ~v19 v20 ~v21 v22 ~v23 v24
  = du_σ_848 v0 v1 v2 v5 v10 v12 v13 v16 v20 v22 v24
du_σ_848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ_848 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_490 (coe v5) (coe v6) (coe v7)) (coe v4)))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)) (coe v9)
      (coe v10)
-- Once.Adequacy.TeleWalk.Invariant._._.old
d_old_850 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_old_850 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
          ~v14 ~v15 v16 ~v17 v18 v19 v20 v21 v22 v23 v24
  = du_old_850 v5 v12 v13 v16 v18 v19 v20 v21 v22 v23 v24
du_old_850 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_old_850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      d_rel_164 v4
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe du_e_490 (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         du_ns'45'step_208 (coe v6)
         (coe
            du_bare'45'ne_178
            (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0)) (coe v5))
         (coe v7))
      v8 v9 v10
-- Once.Adequacy.TeleWalk.Invariant._._.callRel
d_callRel_856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_callRel_856 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13
              ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 v24
  = du_callRel_856 v0 v1 v2 v5 v10 v12 v13 v16 v22 v24
du_callRel_856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_callRel_856 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Denotation.EvalRel.d_coh'45'runs_1322 (coe v6)
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80
            (coe
               MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
               (coe du_φ_16 (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe du_e_490 (coe v5) (coe v6) (coe v7)) (coe v4))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)) (coe v8)
               (coe v9)))
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6))
         (coe
            MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v6)
            (coe
               MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe du_x_476 (coe v5))))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158 (coe v6)
         (coe
            du_M_510 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6) (coe v7)))
      (coe
         MAlonzo.Code.Once.Adequacy.TableCall.du_abi_288 (coe v0)
         (coe du_φ_16 (coe v1) (coe v2)) (coe v6) (coe v4) (coe v7))
-- Once.Adequacy.TeleWalk.Invariant._._.new
d_new_858 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_new_858 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 ~v14 v15
          v16 ~v17 v18 ~v19 v20 ~v21 v22 ~v23 v24
  = du_new_858
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v15 v16 v18 v20 v22 v24
du_new_858 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_new_858 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_GM'45'D_1246 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Meaning.du_'10214'_'10215'_502 v1
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v1)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe
                        MAlonzo.Code.Once.Compile.d_telePolys_418
                        (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5))))
                  (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v11)) (coe v12)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_V_496 (coe v5) (coe v7) (coe v8) (coe v9)) (coe v13)))
         v12 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe
            du_Dc_498 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
            (coe v9) (coe v11) (coe v12) (coe v13))
         v0
         (coe
            du_δ_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158 (coe v12)
         (coe
            du_M_510 (coe v0) (coe v1) (coe v2) (coe v10) (coe v12) (coe v14)))
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.d_callSD_1962 (coe v0)
         (coe
            du_σ_848 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v11)
            (coe v12) (coe v14) (coe v16) (coe v17) (coe v18))
         (coe du_x_476 (coe v11)) (coe v12))
      (coe
         du_relM_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
         (coe v13) (coe v14) (coe v15))
      (coe
         du_callRel_856 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10)
         (coe v11) (coe v12) (coe v14) (coe v17) (coe v18))
-- Once.Adequacy.TeleWalk.Invariant.inv-poly
d_inv'45'poly_892 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
d_inv'45'poly_892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
  = du_inv'45'poly_892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inv'45'poly_892 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> T_Inv_120
du_inv'45'poly_892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         (\ v13 v14 v15 ->
            coe
              C_constructor_166 (coe d_irf_152 (coe v14))
              (coe d_irs_154 (coe v14))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                 (coe
                    MAlonzo.Code.Once.Adequacy.TelePosition.du_iself'45'step_168
                    (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5))
                    (coe du_frT_944 (coe v5) (coe v15)) (coe d_iself_156 (coe v14))))
              (coe
                 du_rel'8242'_952 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                 (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                 (coe v13) (coe v14) (coe v15))))
-- Once.Adequacy.TeleWalk.Invariant._.y
d_y_922 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_y_922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
        ~v14 ~v15
  = du_y_922 v12
du_y_922 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_y_922 v0 = coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._.scT
d_scT_924 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_scT_924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15
  = du_scT_924 v12
du_scT_924 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
du_scT_924 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._.bodyT
d_bodyT_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
d_bodyT_926 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            ~v15
  = du_bodyT_926 v1 v3 v4 v5 v7 v8 v9 v12 v13
du_bodyT_926 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
du_bodyT_926 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
      (coe
         MAlonzo.Code.Once.Lang.Type.Instance.d_arityOf_88
         (coe du_scT_924 (coe v7)))
      (coe
         MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
         (coe du_scT_924 (coe v7)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Lang.Core.Translate.d_polyElab_720 (coe v0)
            (coe v1) (coe v2)
            (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
            (coe v7) (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe v4) (coe v5) (coe v6) (coe v8)))
-- Once.Adequacy.TeleWalk.Invariant._.bodyD
d_bodyD_928 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_bodyD_928 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
            ~v15
  = du_bodyD_928 v1 v3 v4 v5 v7 v8 v9 v12 v13
du_bodyD_928 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_bodyD_928 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Lang.Core.Translate.du_polyBody_740 (coe v0)
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v3))
      (coe v7) (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
      (coe v4) (coe v5) (coe v6) (coe v8)
-- Once.Adequacy.TeleWalk.Invariant._.S′
d_S'8242'_930 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
d_S'8242'_930 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              ~v13 ~v14 ~v15
  = du_S'8242'_930 v4 v12
du_S'8242'_930 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
du_S'8242'_930 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v0
      (MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
         (coe du_scT_924 (coe v1)))
-- Once.Adequacy.TeleWalk.Invariant._.δ
d_δ_932 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ_932 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
        ~v15
  = du_δ_932 v0 v1 v2 v3 v4 v6
du_δ_932 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ_932 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
      (coe v3) (coe v4) (coe v0) (coe v2) (coe v5)
-- Once.Adequacy.TeleWalk.Invariant._.δ′
d_δ'8242'_934 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_δ'8242'_934 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12 v13 ~v14
              ~v15
  = du_δ'8242'_934 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12 v13
du_δ'8242'_934 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
du_δ'8242'_934 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v3))
      (coe
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v4
         (MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
            (coe du_scT_924 (coe v10))))
      (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v6
         (coe
            du_bodyT_926 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
            (coe v9) (coe v10) (coe v11))
         (coe
            du_bodyD_928 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
            (coe v9) (coe v10) (coe v11)))
-- Once.Adequacy.TeleWalk.Invariant._.ctx
d_ctx_936 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_936 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_ctx_936 v5
du_ctx_936 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_936 v0
  = coe
      MAlonzo.Code.Once.Lang.Module.d_ctxOf_24
      (coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))
-- Once.Adequacy.TeleWalk.Invariant._.ρ
d_ρ_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
d_ρ_938 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_ρ_938 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_ρ_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
du_ρ_938 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.CoreEnv.du_envOf_306 (coe v1)
      (coe
         du_δ_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_418
         (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
      (coe v7) (coe v8) (coe v9)
-- Once.Adequacy.TeleWalk.Invariant._.V
d_V_940 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
d_V_940 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
        ~v14 ~v15
  = du_V_940 v5 v7 v8 v9
du_V_940 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516
du_V_940 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Translate.du_viewOf_562
      (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_418
         (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v0)))
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.TeleWalk.Invariant._.frT
d_frT_944 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frT_944 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15
  = du_frT_944 v5 v15
du_frT_944 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_frT_944 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_'43''43''8315''691'_200
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
         (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v0)))
      (coe v1)
-- Once.Adequacy.TeleWalk.Invariant._.rel′
d_rel'8242'_952 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rel'8242'_952 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20
  = du_rel'8242'_952
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      v20
du_rel'8242'_952 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rel'8242'_952 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = case coe v18 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v22 v23
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   du_head_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                   (coe v13) (coe v15) (coe v16) (coe v17) (coe v23) (coe v19))
                (coe
                   MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_envrel'45'transport_296
                   (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v5))
                   (coe
                      MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_92
                      (coe
                         MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36 (coe v1)
                         (coe addInt (coe (1 :: Integer)) (coe v3))
                         (coe
                            MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v4
                            (MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
                               (coe du_scT_924 (coe v11))))
                         (coe v0) (coe v2)
                         (coe
                            MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v6
                            (coe
                               du_bodyT_926 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
                               (coe v9) (coe v11) (coe v12))
                            (coe
                               du_bodyD_928 (coe v1) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
                               (coe v9) (coe v11) (coe v12))))
                      (coe
                         MAlonzo.Code.Once.Compile.d_telePolys_418
                         (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
                      (coe
                         MAlonzo.Code.Once.Lang.Core.Translate.du_wkT_176
                         (coe
                            MAlonzo.Code.Once.Compile.d_telePolys_418
                            (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
                         (coe v9)))
                   (coe
                      du_ra_984 (coe MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5))
                      (coe du_frT_944 (coe v5) (coe v14)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         du_old_976 (coe v13) (coe v15) (coe v16) (coe v17) (coe v23)
                         (coe v19)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_imprel'45'transport_352
                   (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5))
                   (coe
                      MAlonzo.Code.Once.Denotation.Meaning.d_entries_316
                      (coe
                         du_ρ_938 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8) (coe v9)))
                   (coe
                      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.du_calls'45'same_652
                      (coe MAlonzo.Code.Once.Compile.d_cimps_406 (coe v5)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            du_old_976 (coe v13) (coe v15) (coe v16) (coe v17) (coe v23)
                            (coe v19)))))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant._._.tbl
d_tbl_970 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tbl_970 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tbl_970 v10 v16
du_tbl_970 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_tbl_970 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0)
-- Once.Adequacy.TeleWalk.Invariant._._.σo
d_σo_972 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σo_972 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 v16 ~v17 v18 ~v19 ~v20 v21
  = du_σo_972 v0 v1 v2 v5 v10 v16 v18 v21
du_σo_972 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σo_972 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe du_tbl_970 (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)) (coe v6)
      (coe v7)
-- Once.Adequacy.TeleWalk.Invariant._._.σ
d_σ_974 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ_974 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 ~v13 ~v14
        ~v15 v16 ~v17 v18 ~v19 ~v20 v21
  = du_σ_974 v0 v1 v2 v5 v10 v12 v16 v18 v21
du_σ_974 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ_974 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW_18 (coe v0)
      (coe du_φ_16 (coe v1) (coe v2)) (coe du_tbl_970 (coe v4) (coe v6))
      (coe
         MAlonzo.Code.Once.Compile.d_cpolys_420
         (coe MAlonzo.Code.Once.Compile.d_addEntry_490 (coe v3) (coe v5)))
      (coe v7) (coe v8)
-- Once.Adequacy.TeleWalk.Invariant._._.old
d_old_976 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_old_976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 v14 ~v15 v16 v17 v18 ~v19 v20 v21
  = du_old_976 v14 v16 v17 v18 v20 v21
du_old_976 ::
  T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_old_976 v0 v1 v2 v3 v4 v5 = coe d_rel_164 v0 v1 v2 v3 v4 v5
-- Once.Adequacy.TeleWalk.Invariant._._.ra
d_ra_984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_ra_984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
  = du_ra_984 v22 v23
du_ra_984 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_ra_984 v0 v1
  = case coe v0 of
      [] -> coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_ra_984 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant._._.head
d_head_1000 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_head_1000 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 v14 ~v15
            v16 v17 v18 ~v19 v20 v21 v22 v23
  = du_head_1000
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v16 v17 v18 v20 v21
      v22 v23
du_head_1000 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_head_1000 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16 v17 v18 v19 v20
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_GM'45'D_1246 (coe v0)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v19)
      (coe
         MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_352
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_sig_14
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_imps_16
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
            (coe
               MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_tele_18
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))))
         (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v11)) (coe v19)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (coe
            du_D'45'U_1010 (coe v5) (coe v11) (coe v12) (coe v13) (coe v20))
         (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Meaning.C_meanings_326
            (coe
               MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_92
               (coe
                  du_δ_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
               (coe
                  MAlonzo.Code.Once.Compile.d_telePolys_418
                  (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
               (coe v9))
            (coe
               MAlonzo.Code.Once.Denotation.Meaning.d_entries_316
               (coe
                  du_ρ_938 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9)))
            (coe
               MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Core.Meaning.d_impl_376
                  (coe
                     du_δ_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))))
            (coe
               (\ v21 v22 v23 ->
                  MAlonzo.Code.Once.Lang.Elaboration.d_member_486
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Translate.du_sigAt_396
                       (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)) (coe v7)
                       (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v21))))))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_sig_14
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_imps_16
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_tele_18
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))))
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_sig_14
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_imps_16
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_tele_18
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))))
         (coe v19)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_sig_14
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_imps_16
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
               (coe
                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                  (coe
                     MAlonzo.Code.Once.Lang.Module.d_tele_18
                     (coe
                        MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))))
            (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v11)) (coe v19)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe
               du_D'45'U_1010 (coe v5) (coe v11) (coe v12) (coe v13) (coe v20)))
         (coe v0)
         (coe
            du_σo_972 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v14)
            (coe v16) (coe v18))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_refs_86
         (coe
            du_σ_974 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v11)
            (coe v14) (coe v16) (coe v18))
         (coe du_y_922 (coe v11)) v19)
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.d_bridge'45'c_2122
         (coe v0)
         (coe
            du_σo_972 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10) (coe v14)
            (coe v16) (coe v18))
         (coe
            MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW'45'self_706 (coe v0)
            (coe du_φ_16 (coe v1) (coe v2))
            (coe du_tbl_970 (coe v10) (coe v14))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v5)) (coe v16)
            (coe v18))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_sig_14
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_imps_16
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5))))
            (coe
               MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
               (coe
                  MAlonzo.Code.Once.Lang.Module.d_tele_18
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v5)))))
         (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v11)) (coe v19)
         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
         (coe
            du_D'45'U_1010 (coe v5) (coe v11) (coe v12) (coe v13) (coe v20))
         (coe
            MAlonzo.Code.Once.Denotation.Meaning.C_meanings_326
            (coe
               MAlonzo.Code.Once.Adequacy.CoreEnv.du_defEnv_92
               (coe
                  du_δ_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
               (coe
                  MAlonzo.Code.Once.Compile.d_telePolys_418
                  (MAlonzo.Code.Once.Compile.d_ctele_408 (coe v5)))
               (coe v9))
            (coe
               MAlonzo.Code.Once.Denotation.Meaning.d_entries_316
               (coe
                  du_ρ_938 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                  (coe v6) (coe v7) (coe v8) (coe v9)))
            (coe
               MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Core.Meaning.d_impl_376
                  (coe
                     du_δ_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))))
            (coe
               (\ v21 v22 v23 ->
                  MAlonzo.Code.Once.Lang.Elaboration.d_member_486
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Translate.du_sigAt_396
                       (coe MAlonzo.Code.Once.Compile.d_csig_404 (coe v5)) (coe v7)
                       (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v21))))))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Once.Adequacy.MeaningBridge.C_mk'8638'_184
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe
            du_old_976 (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
            (coe v18)))
      (coe
         du_relSD_1020 (coe v0) (coe v1) (coe v2) (coe v5) (coe v10)
         (coe v11) (coe v12) (coe v13) (coe v14) (coe v16) (coe v18)
         (coe v19) (coe v20))
-- Once.Adequacy.TeleWalk.Invariant._._._.D-U
d_D'45'U_1010 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'45'U_1010 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
              v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_D'45'U_1010 v5 v12 v13 v14 v23
du_D'45'U_1010 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'45'U_1010 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_24
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
         (coe
            MAlonzo.Code.Once.Lang.Module.d_sig_14
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
         (coe
            MAlonzo.Code.Once.Lang.Module.d_imps_16
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
      (coe
         MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
         (coe
            MAlonzo.Code.Once.Lang.Module.d_tele_18
            (coe
               MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
      (coe du_scT_924 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_irf_152 (coe v3)) (coe d_irs_154 (coe v3)))
      (coe v2) (coe v4)
-- Once.Adequacy.TeleWalk.Invariant._._._.ccU
d_ccU_1012 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccU_1012 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
           v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
  = du_ccU_1012 v5 v12 v13 v14 v22 v23
du_ccU_1012 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccU_1012 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_2644
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
            (coe
               MAlonzo.Code.Once.Lang.Module.d_sig_14
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))
            (coe
               MAlonzo.Code.Once.Lang.Module.d_imps_16
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0))))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
            (coe
               MAlonzo.Code.Once.Lang.Module.d_tele_18
               (coe
                  MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270 (coe v0)))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1)) (coe v4)
      (coe du_D'45'U_1010 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Adequacy.TeleWalk.Invariant._._._.ce
d_ce_1014 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_1014 = erased
-- Once.Adequacy.TeleWalk.Invariant._._._.cr
d_cr_1016 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cr_1016 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_cr_1016 v5 v12 v22
du_cr_1016 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cr_1016 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6334
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
         (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v0))
         (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v0)))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1)) (coe v2)
-- Once.Adequacy.TeleWalk.Invariant._._._.D′
d_D'8242'_1018 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_1018 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_D'8242'_1018 v5 v12 v22
du_D'8242'_1018 ::
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_1018 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_388
      (coe du_cr_1016 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.TeleWalk.Invariant._._._.relSD
d_relSD_1020 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Lang.Core.Translate.T_TeleSig_110 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_relSD_1020 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 v13
             v14 ~v15 v16 ~v17 v18 ~v19 ~v20 v21 v22 v23
  = du_relSD_1020 v0 v1 v2 v5 v10 v12 v13 v14 v16 v18 v21 v22 v23
du_relSD_1020 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_Inv_120 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_relSD_1020 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.Coherence.d_realize'45'invariant_1130
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
            (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3)))
         (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
            (coe MAlonzo.Code.Once.Compile.d_ctop_414 (coe v3))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v5)) (coe v11)
      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
      (coe du_D'8242'_1018 (coe v3) (coe v5) (coe v11))
      (coe du_D'45'U_1010 (coe v3) (coe v5) (coe v6) (coe v7) (coe v12))
      (coe
         du_σo_972 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
         (coe v9) (coe v10))
      (coe
         MAlonzo.Code.Once.Adequacy.TeleEnvLemmas.d_σW'45'self_706 (coe v0)
         (coe du_φ_16 (coe v1) (coe v2)) (coe du_tbl_970 (coe v4) (coe v8))
         (coe MAlonzo.Code.Once.Compile.d_cpolys_420 (coe v3)) (coe v9)
         (coe v10))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.TeleWalk.Invariant.mainIn-name
d_mainIn'45'name_1042 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_mainIn'45'name_1042 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mainIn'45'name_1042 v4 v5 v6
du_mainIn'45'name_1042 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_mainIn'45'name_1042 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v5 v9 v10 v11 v12
        -> case coe v0 of
             (:) v13 v14
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_mainIn'45'name_1042 (coe v14) (coe v12) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v5 v6 v8 v13 v14 v15
        -> case coe v0 of
             (:) v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                      -> coe
                           seq (coe v18)
                           (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                           (coe du_mainIn'45'name_1042 (coe v17) (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v6 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_mainIn'45'name_1042 (coe v11) (coe v9) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.not-in
d_not'45'in_1068 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45'in_1068 = erased
-- Once.Adequacy.TeleWalk.Invariant.NS
d_NS_1078 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 -> ()
d_NS_1078 = erased
-- Once.Adequacy.TeleWalk.Invariant.ns-of
d_ns'45'of_1094 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ns'45'of_1094 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_ns'45'of_1094 v4 v5
du_ns'45'of_1094 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ns'45'of_1094 v0 v1
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
                    (\ v8 -> coe v6 erased) (coe du_ns'45'of_1094 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleWalk.Invariant.later-ns
d_later'45'ns_1128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Compile.T_CScope_396 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_later'45'ns_1128 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_later'45'ns_1128 v4 v5 v6 v7 v9
du_later'45'ns_1128 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_later'45'ns_1128 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bnil_16 -> coe v4
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v7 v9 v10 v11 v17
        -> case coe v0 of
             (:) v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v22 v23
                      -> coe
                           du_later'45'ns_1128 (coe v19) (coe v17) (coe v2) (coe v23) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_70 v8 v9 v10 v11 v12 v13 v14 v19 v23
        -> case coe v0 of
             (:) v24 v25
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v28 v29
                      -> coe
                           du_later'45'ns_1128 (coe v25) (coe v23) (coe v2) (coe v29)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe du_ns'45'of_1094 (coe v2) (coe v28)) v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_90 v8 v9 v10 v11 v14
        -> case coe v0 of
             (:) v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                      -> coe
                           du_later'45'ns_1128 (coe v16) (coe v14) (coe v2) (coe v20) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
