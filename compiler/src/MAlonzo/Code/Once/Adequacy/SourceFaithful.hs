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

module MAlonzo.Code.Once.Adequacy.SourceFaithful where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CoerceFaithful
import qualified MAlonzo.Code.Once.Adequacy.EnvRel
import qualified MAlonzo.Code.Once.Adequacy.FaithfulLemmas
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.SourceFaithful._.Now
d_Now_22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 -> AgdaAny -> ()
d_Now_22 = erased
-- Once.Adequacy.SourceFaithful.σ₀
d_σ'8320'_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ'8320'_92 v0 v1 ~v2 = du_σ'8320'_92 v0 v1
du_σ'8320'_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
du_σ'8320'_92 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful.≡ˡ
d_'8801''737'_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''737'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8801''737'_106 v10
du_'8801''737'_106 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''737'_106 v0 = coe v0
-- Once.Adequacy.SourceFaithful.subst-T-return∞
d_subst'45'T'45'return'8734'_118 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'return'8734'_118 = erased
-- Once.Adequacy.SourceFaithful.proj₂-subst
d_proj'8322''45'subst_136 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8322''45'subst_136 = erased
-- Once.Adequacy.SourceFaithful.sigOp-rel
d_sigOp'45'rel_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_sigOp'45'rel_150 v0 v1 ~v2 v3 v4 v5 v6 ~v7 ~v8
  = du_sigOp'45'rel_150 v0 v1 v3 v4 v5 v6
du_sigOp'45'rel_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_sigOp'45'rel_150 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'embed_764
      (coe
         MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1))
            (coe v2) (coe v3) (coe v4)
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
               (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
               (coe v5)))
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Once.Lang.Trace.C_ret_114
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                    (coe v6)))))
      (coe
         MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1))
            (coe v2) (coe v3) (coe v4)
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
               (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
               (coe v5)))
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Once.Lang.Trace.C_ret_114
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                    (coe v6)))))
      (coe
         MAlonzo.Code.Once.Denotation.EvalRel.du_RelT'8242''45'refl_284
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.d_base'45'refl_420 (coe v3)
            (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4)))
         (coe
            MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
               (coe MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1))
               (coe v2) (coe v3) (coe v4)
               (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                  (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
                  (coe v5)))
            (coe
               (\ v6 ->
                  coe
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                       (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                       (coe v6))))))
-- Once.Adequacy.SourceFaithful.now-restrict
d_now'45'restrict_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_now'45'restrict_176 = erased
-- Once.Adequacy.SourceFaithful.now-bindEnv
d_now'45'bindEnv_274 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_now'45'bindEnv_274 = erased
-- Once.Adequacy.SourceFaithful.now-branch
d_now'45'branch_324 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_now'45'branch_324 = erased
-- Once.Adequacy.SourceFaithful.proj-lookup
d_proj'45'lookup_350 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'lookup_350 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-id
d_restrict'7472''45'id_382 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'id_382 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-subst
d_restrict'7472''45'subst_436 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'subst_436 = erased
-- Once.Adequacy.SourceFaithful.liftFn-substΦ
d_liftFn'45'substΦ_464 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'substΦ_464 = erased
-- Once.Adequacy.SourceFaithful.substΦ-rel
d_substΦ'45'rel_488 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_substΦ'45'rel_488 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_substΦ'45'rel_488 v4 v5 v6 v7 v11
du_substΦ'45'rel_488 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny -> AgdaAny
du_substΦ'45'rel_488 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful.distribute-red₁
d_distribute'45'red'8321'_526 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'red'8321'_526 = erased
-- Once.Adequacy.SourceFaithful.distribute-red₂
d_distribute'45'red'8322'_554 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'red'8322'_554 = erased
-- Once.Adequacy.SourceFaithful.distribIR-red₁
d_distribIR'45'red'8321'_582 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribIR'45'red'8321'_582 = erased
-- Once.Adequacy.SourceFaithful.distribIR-red₂
d_distribIR'45'red'8322'_610 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribIR'45'red'8322'_610 = erased
-- Once.Adequacy.SourceFaithful.app-rel
d_app'45'rel_638 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_app'45'rel_638 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_app'45'rel_638 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_app'45'rel_638 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_app'45'rel_638 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
            (coe v4))
         (coe v6) (coe v8))
      (coe v9)
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
              (coe
                 (\ v14 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                         (coe v14))))))
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v13
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
         (coe v10))
      (coe v11)
      (coe
         (\ v13 v14 v15 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
              (coe v10)
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13) (coe v16))))
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v16
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v16))))
              (coe v14) (coe v12)
              (coe
                 (\ v16 v17 v18 ->
                    coe
                      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                      (coe v15 v16 v17 v18)))))
-- Once.Adequacy.SourceFaithful.app-rel₁
d_app'45'rel'8321'_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_app'45'rel'8321'_692 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13
  = du_app'45'rel'8321'_692
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_app'45'rel'8321'_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_app'45'rel'8321'_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v5))
            (coe v4))
         (coe v6) (coe v8))
      (coe v9)
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
              (coe
                 (\ v14 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                         (coe v14))))))
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v13
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
         (coe v10))
      (coe v11)
      (coe
         (\ v13 v14 v15 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
              (coe v10)
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13) (coe v16))))
              (coe
                 (\ v16 ->
                    coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v16
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v16))))
              (coe v14) (coe v12)
              (coe
                 (\ v16 v17 v18 ->
                    coe
                      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                      (coe v15 v16 v17 v18)))))
-- Once.Adequacy.SourceFaithful.arith-rel
d_arith'45'rel_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_arith'45'rel_748 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14
  = du_arith'45'rel_748
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_arith'45'rel_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_arith'45'rel_748 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v7) (coe v9))
      (coe v10)
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v4) (coe v8) (coe v9))
              (coe
                 (\ v15 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                         (coe v15))))))
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_embed_136
              (coe
                 MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v6)))
                 (coe
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106 v0
                    (MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1))
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4)) v5
                    v6
                    (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                       (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v6))
                       (coe v14))))))
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
              (coe v11)
              (coe
                 (\ v15 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                      (coe v5) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                         (coe v15))))))
      (coe v12)
      (coe
         (\ v14 v15 v16 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
              (coe
                 MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                 (coe v1) (coe v2) (coe v4) (coe v8) (coe v9))
              (coe v11)
              (coe
                 (\ v17 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14) (coe v17))))
              (coe
                 (\ v17 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_embed_136
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                            (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v6)))
                         (coe
                            MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106 v0
                            (MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1))
                            (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4)) v5
                            v6
                            (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                               (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                               (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v6))
                               (coe v17))))))
              (coe
                 (\ v17 ->
                    MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                      (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                      (coe v5) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15) (coe v17))))
              (coe v13)
              (coe
                 (\ v17 v18 v19 ->
                    coe
                      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                      (coe
                         du_sigOp'45'rel_150 (coe v0) (coe v1)
                         (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v4))
                         (coe v5) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                            (coe v17)))))))
-- Once.Adequacy.SourceFaithful.unop-rel
d_unop'45'rel_798 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_unop'45'rel_798 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_unop'45'rel_798 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10
du_unop'45'rel_798 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_unop'45'rel_798 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v6) (coe v7))
      (coe v8)
      (coe
         (\ v10 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_embed_136
              (coe
                 MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v4) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v5)))
                 (coe
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106 v0
                    (MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22 (coe v1)) v3 v4
                    v5
                    (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                       (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v5))
                       (coe v10))))))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104 (coe v3)
         (coe v4) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v5))
      (coe v9)
      (\ v10 v11 v12 ->
         coe
           du_sigOp'45'rel_150 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
           v10)
-- Once.Adequacy.SourceFaithful.post-rel
d_post'45'rel_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_post'45'rel_842 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 ~v8 v9 v10 v11 v12 v13
  = du_post'45'rel_842 v0 v1 v3 v4 v7 v9 v10 v11 v12 v13
du_post'45'rel_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_post'45'rel_842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v5) (coe v6))
      (coe v7)
      (coe
         (\ v10 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70 (coe v4 v10)))
      (coe
         (\ v10 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70 (coe v4 v10)))
      (coe v9)
      (coe
         (\ v10 v11 v12 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe v8 v10 v11 v12)))
-- Once.Adequacy.SourceFaithful.apply-path
d_apply'45'path_900 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_apply'45'path_900 v0 v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 ~v12
                    v13 ~v14 ~v15 v16 ~v17 v18 v19
  = du_apply'45'path_900 v0 v1 v3 v4 v8 v9 v10 v13 v16 v18 v19
du_apply'45'path_900 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_apply'45'path_900 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
         (coe v7)
         (coe
            (\ v11 ->
               coe
                 MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v11))))
         (coe
            (\ v11 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v11
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11))))
         (coe v8) (coe v9)
         (coe
            (\ v11 v12 v13 ->
               coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                 (coe v10 v11 v12 v13))))
-- Once.Adequacy.SourceFaithful.faithful
d_faithful_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_faithful_950 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe
                MAlonzo.Code.Once.Adequacy.EnvRel.du_lookup'45'rel_94 (coe v4)
                (coe v13) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v14 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v24 v25
                      -> case coe v24 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> coe
                                  seq (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                        (coe
                                           d_faithful_950 (coe v0) (coe v1) (coe v2)
                                           (coe addInt (coe (1 :: Integer)) (coe v3))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4)
                                              (coe v21))
                                           (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v24 v5)
                                           (coe v23) (coe v20) (coe v8) (coe v9) (coe v10))))
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                 (coe
                                                    d_faithful_950 (coe v0) (coe v1) (coe v2)
                                                    (coe addInt (coe (1 :: Integer)) (coe v3))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                       (coe v4) (coe v21))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                                                       v14 v5)
                                                    (coe v23) (coe v20) (coe v8) (coe v9)
                                                    (coe v10))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               d_faithful_950
                                                 (coe v0) (coe v1) (coe v2)
                                                 (coe addInt (coe (1 :: Integer)) (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                    (coe v4) (coe v21))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v14
                                                    v5)
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                 (coe
                                                    d_faithful_950 (coe v0) (coe v1) (coe v2)
                                                    (coe addInt (coe (1 :: Integer)) (coe v3))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                       (coe v4) (coe v21))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                                                       v14 v5)
                                                    (coe v23) (coe v20) (coe v8) (coe v9)
                                                    (coe v10))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               d_faithful_950
                                                 (coe v0) (coe v1) (coe v2)
                                                 (coe addInt (coe (1 :: Integer)) (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                    (coe v4) (coe v21))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v14
                                                    v5)
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               d_faithful_950
                                                 (coe v0) (coe v1) (coe v2)
                                                 (coe addInt (coe (1 :: Integer)) (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                    (coe v4) (coe v21))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v14
                                                    v5)
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v13 v14 v15 v17 v18 v19
        -> case coe v17 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v13)))
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                          (coe v4) (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v6))
                          (coe v18))
                       (coe v8))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe v18) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                            (coe
                               MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                            (coe
                               (\ v21 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                                       (coe v21))))))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v20
                            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v20))))
                    (coe
                       (\ v20 -> coe v20 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                    (coe
                       d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe v18) (coe v8)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9))
                       (coe
                          du_substΦ'45'rel_488 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v10)))
                    (coe
                       (\ v20 v21 ->
                          coe MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    du_app'45'rel'8321'_692 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))))
                    (coe v15) (coe v6)
                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                (coe v13))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                          (coe v4) (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v6))
                          (coe v18))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13) (coe du_leF_1284 (coe v13) (coe v14))))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                (coe v14))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                          (coe v4) (coe v14) (coe v15) (coe v19))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v14) (coe du_leX_1286 (coe v13) (coe v14))))
                    (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe v18) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4) (coe v15) (coe v19) (coe v0)
                       (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                                (coe v14))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))))
                          (coe v9)))
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                             (coe v14)))
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe du_leF_1284 (coe v13) (coe v14)) (coe v18) (coe v8) (coe v9)
                       (coe v10))
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                             (coe v14)))
                       (coe v14) (coe v15) (coe du_leX_1286 (coe v13) (coe v14)) (coe v19)
                       (coe v8) (coe v9) (coe v10))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    du_app'45'rel_638 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))))
                    (coe v15) (coe v6)
                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                (coe v13))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                          (coe v4) (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v6))
                          (coe v18))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13) (coe du_leF_1310 (coe v13) (coe v14))))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                (coe v14))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                          (coe v4) (coe v14) (coe v15) (coe v19))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v14) (coe du_leX_1312 (coe v13) (coe v14))))
                    (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe v18) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4) (coe v15) (coe v19) (coe v0)
                       (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                (coe v14))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                (coe v14))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))))
                          (coe v9)))
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                             (coe v14)))
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v17)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v6))
                       (coe du_leF_1310 (coe v13) (coe v14)) (coe v18) (coe v8) (coe v9)
                       (coe v10))
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v17)
                             (coe v14)))
                       (coe v14) (coe v15) (coe du_leX_1312 (coe v13) (coe v14)) (coe v19)
                       (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v13 v14 v15 v18 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                           (coe
                              (\ v26 v27 v28 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                   (coe
                                      du_app'45'rel_638 (coe v0) (coe v1)
                                      (coe du_Δ_1338 (coe v4) (coe v13) (coe v14)) (coe v15)
                                      (coe v23) (coe v25)
                                      (coe
                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                  (coe v4) (coe v13))))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
                                            (coe v3) (coe v4) (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v15)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v25))
                                               (coe v23))
                                            (coe v19))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe v13) (coe du_leF_1340 (coe v13) (coe v14))))
                                      (coe
                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                  (coe v4) (coe v14))))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
                                            (coe v3) (coe v4) (coe v14) (coe v15) (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe v14) (coe du_leX_1342 (coe v13) (coe v14))))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                         (coe v3) (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v25))
                                            (coe v23))
                                         (coe v19) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe v9)))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                         (coe v3) (coe v4) (coe v15) (coe v20) (coe v0)
                                         (coe du_σ'8320'_92 (coe v0) (coe v1))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                            (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                               (coe v14)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v14)))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v14))))
                                            (coe v9)))
                                      (coe
                                         d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v25))
                                            (coe v23))
                                         (coe du_leF_1340 (coe v13) (coe v14)) (coe v19) (coe v8)
                                         (coe v9) (coe v10))
                                      (coe
                                         d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14)))
                                         (coe v14) (coe v15) (coe du_leX_1342 (coe v13) (coe v14))
                                         (coe v20) (coe v8) (coe v9) (coe v10)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v13 v14 v17 v18
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v19 v20
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                (coe v14))))
                       (coe v19)
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                   (coe v13))))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                             (coe v4) (coe v13) (coe v19) (coe v17))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                (coe v14))
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v13) (coe v14))))
                       (coe v8))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4) (coe v19) (coe v17) (coe v0)
                       (coe du_σ'8320'_92 (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v9)))
                    (coe
                       (\ v21 ->
                          coe
                            MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                            (coe
                               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                               (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))))
                               (coe v20)
                               (coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                           (coe v14))))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                                     (coe v4) (coe v14) (coe v20) (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13) (coe v14))))
                               (coe v8))
                            (coe
                               (\ v22 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v22))))))
                    (coe
                       (\ v21 ->
                          coe
                            MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v3) (coe v4) (coe v20) (coe v18) (coe v0)
                               (coe du_σ'8320'_92 (coe v0) (coe v1))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v9)))
                            (coe
                               (\ v22 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v22))))))
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                          (coe v14))
                       (coe v13) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                          (coe v13) (coe v14))
                       (coe v17) (coe v8) (coe v9) (coe v10))
                    (coe
                       (\ v21 v22 v23 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                            (coe
                               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                               (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))))
                               (coe v20)
                               (coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                           (coe v14))))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                                     (coe v4) (coe v14) (coe v20) (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13) (coe v14))))
                               (coe v8))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v3) (coe v4) (coe v20) (coe v18) (coe v0)
                               (coe du_σ'8320'_92 (coe v0) (coe v1))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v9)))
                            (coe
                               (\ v24 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v24))))
                            (coe
                               (\ v24 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v22)
                                       (coe v24))))
                            (coe
                               d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                  (coe v14))
                               (coe v14) (coe v20)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                  (coe v13) (coe v14))
                               (coe v18) (coe v8) (coe v9) (coe v10))
                            (coe
                               (\ v24 v25 v26 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v23)
                                       (coe v26))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v15 v16
        -> coe
             du_post'45'rel_842 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v15))
             (coe (\ v17 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v17)))
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16))
             (coe v8)
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (coe
                (\ v17 v18 v19 ->
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v19)))
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16) (coe v8) (coe v9) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v14 v16
        -> coe
             du_post'45'rel_842 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v14) (coe v6))
             (coe (\ v17 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v17)))
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16))
             (coe v8)
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (coe
                (\ v17 v18 v19 ->
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v19)))
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16) (coe v8) (coe v9) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
               -> coe
                    du_post'45'rel_842 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
                    (coe v17) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe
                       MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                       (coe v4) (coe v5) (coe v17) (coe v16))
                    (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4) (coe v17) (coe v16) (coe v0)
                       (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
                    (coe (\ v19 v20 v21 -> v21))
                    (coe
                       d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v17) (coe v16) (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
               -> coe
                    du_post'45'rel_842 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
                    (coe v18) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe
                       MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                       (coe v4) (coe v5) (coe v18) (coe v16))
                    (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v3) (coe v4) (coe v18) (coe v16) (coe v0)
                       (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
                    (coe (\ v19 v20 v21 -> v21))
                    (coe
                       d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v18) (coe v16) (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v13 v14 v15 v16 v17 v18 v19 v21 v22 v23
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                (coe
                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                   (coe
                      (\ v24 ->
                         coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                    (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe du_leAll_2064 (coe v13) (coe v14) (coe v15)) (coe v8))
                           (coe v24)))
                   (coe
                      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                      (coe v1)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                  (coe v15)))))
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                      (coe
                         MAlonzo.Code.Once.IR.C__'8728'__28
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                  (coe v13))))
                         (coe
                            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                            (coe v4) (coe v13)
                            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                            (coe v21))
                         (coe
                            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                  (coe v15)))
                            (coe v13) (coe du_leS_2066 (coe v13) (coe v14) (coe v15))))
                      (coe v8)))
                (coe
                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                   (coe v3) (coe v4)
                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                   (coe v21) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                   (coe
                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                            (coe v15)))
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                         (coe v13)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                            (coe v15)))
                      (coe v9)))
                (coe
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                   (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                      (coe du_Δ_2062 (coe v4) (coe v14) (coe v15))
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19)))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'43'__26
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                         (coe du_Δ_2062 (coe v4) (coe v14) (coe v15)) (coe v18))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                         (coe du_Δ_2062 (coe v4) (coe v14) (coe v15)) (coe v19)))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_distribute_270
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe du_Δ_2062 (coe v4) (coe v14) (coe v15)))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v18))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v19))))
                (coe
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                   (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.C__'43'__26
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                         (coe du_Δ_2062 (coe v4) (coe v14) (coe v15)) (coe v18))
                      (coe
                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                         (coe du_Δ_2062 (coe v4) (coe v14) (coe v15)) (coe v19)))
                   (coe v6)
                   (coe
                      MAlonzo.Code.Once.IR.C_case_68
                      (coe
                         du_LL_2080 (coe v3) (coe v4) (coe v6) (coe v14) (coe v15) (coe v16)
                         (coe v18) (coe v22))
                      (coe
                         du_RR_2082 (coe v3) (coe v4) (coe v6) (coe v14) (coe v15) (coe v17)
                         (coe v19) (coe v23))))
                (coe
                   MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                   (\ v24 ->
                      coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe addInt (coe (1 :: Integer)) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v18))
                        (coe v6) (coe v22) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v16)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
                                 (coe v14) (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                       (coe v14) (coe v15)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                    (coe v15))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                       (coe v14) (coe v15)))
                                 (coe v9)))
                           (coe v24)))
                   (\ v24 ->
                      coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe addInt (coe (1 :: Integer)) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v19))
                        (coe v6) (coe v23) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v17)
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
                                 (coe v14) (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                       (coe v14) (coe v15)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                    (coe v15))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                       (coe v14) (coe v15)))
                                 (coe v9)))
                           (coe v24))))
                (coe
                   MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                   (coe
                      (\ v24 ->
                         coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                    (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe du_leAll_2064 (coe v13) (coe v14) (coe v15)) (coe v8))
                           (coe v24)))
                   (coe
                      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                      (coe v1)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                  (coe v15)))))
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                      (coe
                         MAlonzo.Code.Once.IR.C__'8728'__28
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                                  (coe v13))))
                         (coe
                            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                            (coe v4) (coe v13)
                            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                            (coe v21))
                         (coe
                            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                                  (coe v15)))
                            (coe v13) (coe du_leS_2066 (coe v13) (coe v14) (coe v15))))
                      (coe v8))
                   (coe
                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                      (coe v3) (coe v4)
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                      (coe v21) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                      (coe
                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                               (coe v15)))
                         (coe v13)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                            (coe v13)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                               (coe v15)))
                         (coe v9)))
                   (coe
                      d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v14)
                            (coe v15)))
                      (coe v13)
                      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v19))
                      (coe du_leS_2066 (coe v13) (coe v14) (coe v15)) (coe v21) (coe v8)
                      (coe v9) (coe v10))
                   (coe
                      (\ v24 v25 v26 ->
                         coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v26))))
                (coe
                   du_'46'extendedlambda0_2102 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v6) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                   (coe v18) (coe v19) (coe v22) (coe v23) (coe v8) (coe v9)
                   (coe v10)))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v15
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
                (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                   (coe v4) (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                   (coe v15))
                (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                (coe v15) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (coe
                MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                (coe v1) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v6)
                (coe MAlonzo.Code.Once.IR.C_initial_76))
             (\ v16 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v15)
                (coe v8) (coe v9) (coe v10))
             (coe
                (\ v16 v17 v18 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v13 v14 v15 v16 v18 v19
        -> case coe v15 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    d_faithful_950 (coe v0) (coe v1) (coe v2)
                    (coe addInt (coe (1 :: Integer)) (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v16))
                    (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15 v14) (coe v6)
                    (coe v19) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v9))
                    (coe
                       du_substΦ'45'rel_488 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v10))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    d_let'45'body_1028 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v13) (coe v14) (coe v16) (coe v6) (coe v15) (coe v18)
                    (coe v19) (coe v8) (coe v9) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                       (coe v13))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    d_let'45'body_1028 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v13) (coe v14) (coe v16) (coe v6) (coe v15) (coe v18)
                    (coe v19) (coe v8) (coe v9) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v13
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                erased)
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v13
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                erased)
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v14
        -> coe
             du_unop'45'rel_798 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v14))
             (coe v8)
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v14) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14)
                (coe v8) (coe v9) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v14
        -> coe
             du_unop'45'rel_798 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124)
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v14))
             (coe v8)
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v14) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14)
                (coe v8) (coe v9) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v13 v14 v15 v16
        -> coe
             d_binop_1000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
             (coe v14) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
             (coe v15) (coe v16) (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Adequacy.CoerceFaithful.d_coerce'45'lift_1044 v0
             v1
             (coe
                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5)))
             v14 v6 v16
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                (coe v4) (coe v5) (coe v14) (coe v17))
             v8
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4) (coe v14) (coe v17) (coe v0)
                (coe du_σ'8320'_92 (coe v0) (coe v1)) (coe v9))
             (d_faithful_950
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                (coe v17) (coe v8) (coe v9) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v14 v15
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C_Unit_20
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C_Void_22
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                    -> case coe v15 of
                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v24 v25
                                           -> coe
                                                du_sigop'45'arr'8320'_1058 (coe v0) (coe v1)
                                                (coe v18)
                                                (coe
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                   (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                   (coe v25))
                                         _ -> erased
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                    -> case coe v15 of
                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v24 v25
                                           -> coe
                                                du_sigop'45'arr'8320'_1058 (coe v0) (coe v1)
                                                (coe v18)
                                                (coe
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                   (coe v18) (coe v17) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                   (coe v25))
                                         _ -> erased
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                    -> case coe v15 of
                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v24 v25
                                           -> coe
                                                du_sigop'45'arr'8320'_1058 (coe v0) (coe v1)
                                                (coe v18)
                                                (coe
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                   (coe v18) (coe v17) (coe v14)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                   (coe v25))
                                         _ -> erased
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                 (coe
                                                    du_sigOp'45'rel_150 (coe v0) (coe v1) (coe v16)
                                                    (coe v18)
                                                    (coe
                                                       du_si_2186 (coe v20) (coe v18) (coe v14)
                                                       (coe v24) (coe v25))
                                                    (coe v26))))
                                  _ -> erased
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                 (coe
                                                    du_sigOp'45'rel_150 (coe v0) (coe v1) (coe v16)
                                                    (coe v18)
                                                    (coe
                                                       du_si_2214 (coe v20) (coe v18) (coe v14)
                                                       (coe v24) (coe v25))
                                                    (coe v26))))
                                  _ -> erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C_Int_34
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C_Float_36
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Lang.Type.C_rigid_38 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigop'45'value_1040 (coe v0) (coe v1) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v14
        -> coe
             du_ref'45'rel_1070 (coe v0) (coe v1) (coe v2) (coe v6) (coe v14)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v13
        -> coe
             du_ref'45'rel_1070 (coe v0) (coe v1) (coe v2) (coe v6) (coe v13)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v14
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_faithful_950 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v6)
                (coe v14) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> coe
                    du_lift'45'morph_1088 (coe v0) (coe v1) (coe v2) (coe v17)
                    (coe v19) (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v13 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13)))))
                (coe v14)
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                            (coe v13))))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                      (coe v4) (coe v13) (coe v14) (coe v17))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13)))
                      (coe v13) (coe du_leM_1972 (coe v3) (coe v13))))
                (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v3) (coe v4) (coe v14) (coe v17) (coe v0)
                (coe du_σ'8320'_92 (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))))
                   (coe v9)))
             (coe
                MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                (coe v1) (coe v14) (coe v6) (coe v16))
             (coe
                (\ v18 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80
                        (coe du_σ'8320'_92 (coe v0) (coe v1)))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)) (coe v16)
                     (coe v18)))
             (coe
                d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                   (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13)))
                (coe v13) (coe v14) (coe du_leM_1972 (coe v3) (coe v13)) (coe v17)
                (coe v8) (coe v9) (coe v10))
             (coe
                MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
                (coe v1) (coe v1) (coe v2) (coe v14) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v13 v14 v16 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                           (coe
                              MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                              (coe v1) (coe du_Δ_1408 (coe v4) (coe v13) (coe v14))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v25))
                                 (coe v23))
                              (coe
                                 du_ef_1416 (coe v3) (coe v4) (coe v13) (coe v14) (coe v16)
                                 (coe v23) (coe v25) (coe v19))
                              (coe v8))
                           (coe
                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                              (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v25))
                                 (coe v23))
                              (coe v19) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v14)))
                                 (coe v9)))
                           (coe
                              (\ v26 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                   (coe
                                      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                      (coe v1) (coe du_Δ_1408 (coe v4) (coe v13) (coe v14))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v16))
                                      (coe
                                         du_eg_1418 (coe v3) (coe v4) (coe v13) (coe v14) (coe v21)
                                         (coe v16) (coe v25) (coe v20))
                                      (coe v8))
                                   (coe
                                      (\ v27 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v26)
                                              (coe v27))))))
                           (coe
                              MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                              (coe v1) (coe du_P_1410 (coe v21) (coe v16) (coe v23) (coe v25))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v25))
                                 (coe v23))
                              (coe
                                 MAlonzo.Code.Once.Surface.Elaborate.du_compIR_320
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v21))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v16))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v23))))
                           (coe
                              (\ v26 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v3) (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14))))
                                         (coe v9)))
                                   (coe
                                      (\ v27 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v28 ->
                                                 coe
                                                   MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                   (coe v27 v28) (coe v26)))))))
                           (coe
                              d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v14)))
                              (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v25))
                                 (coe v23))
                              (coe du_leF_1412 (coe v13) (coe v14)) (coe v19) (coe v8) (coe v9)
                              (coe v10))
                           (coe
                              (\ v26 v27 v28 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                                   (coe
                                      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                      (coe v1) (coe du_Δ_1408 (coe v4) (coe v13) (coe v14))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v16))
                                      (coe
                                         du_eg_1418 (coe v3) (coe v4) (coe v13) (coe v14) (coe v21)
                                         (coe v16) (coe v25) (coe v20))
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v3) (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v14))))
                                         (coe v9)))
                                   (coe
                                      (\ v29 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v26)
                                              (coe v29))))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                      (coe v1)
                                      (coe du_P_1410 (coe v21) (coe v16) (coe v23) (coe v25))
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v23))
                                      (coe
                                         MAlonzo.Code.Once.Surface.Elaborate.du_compIR_320
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v21))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v16))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v23))))
                                   (coe
                                      (\ v29 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v30 ->
                                                 coe
                                                   MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                   (coe v29 v30) (coe v27)))))
                                   (coe
                                      d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v14)))
                                      (coe v14)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v25))
                                         (coe v16))
                                      (coe du_leG_1414 (coe v13) (coe v14)) (coe v20) (coe v8)
                                      (coe v9) (coe v10))
                                   (coe
                                      (\ v29 v30 v31 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                           (coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                              (coe
                                                 (\ v32 v33 v34 ->
                                                    coe
                                                      du_apply'45'path_900 (coe v0) (coe v1)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                         (coe
                                                            du_P_1410 (coe v21) (coe v16) (coe v23)
                                                            (coe v25))
                                                         (coe v21))
                                                      (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.C__'42'__20
                                                            (coe
                                                               MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                  (coe v21))
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                  (coe v16)))
                                                            (coe
                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                               (coe v21)))
                                                         (coe MAlonzo.Code.Once.IR.C_apply_90)
                                                         (coe
                                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                            (coe
                                                               MAlonzo.Code.Once.IR.C__'8728'__28
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                        (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                           (coe v25))
                                                                        (coe v23)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                        (coe v21))
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                        (coe v16))))
                                                               (coe MAlonzo.Code.Once.IR.C_snd_48)
                                                               (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                            (coe MAlonzo.Code.Once.IR.C_snd_48)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v26) (coe v29))
                                                         (coe v32))
                                                      (coe v26) (coe v30 v33) (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                         (coe v31 v32 v33 v34))
                                                      (coe v28))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v13 v14 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v24 v25
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                                  (coe
                                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                     (coe v1) (coe du_Δ_1468 (coe v4) (coe v13) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v27))
                                        (coe v23))
                                     (coe
                                        du_ef_1476 (coe v3) (coe v4) (coe v13) (coe v14) (coe v24)
                                        (coe v23) (coe v27) (coe v19))
                                     (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v27))
                                        (coe v23))
                                     (coe v19) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9)))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_Δ_1468 (coe v4) (coe v13) (coe v14))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe
                                                du_eg_1478 (coe v3) (coe v4) (coe v13) (coe v14)
                                                (coe v25) (coe v23) (coe v27) (coe v20))
                                             (coe v8))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v28) (coe v29))))))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                     (coe v1)
                                     (coe du_P_1470 (coe v24) (coe v25) (coe v23) (coe v27))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v27))
                                        (coe v23))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Elaborate.du_copairIR_332
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v24))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v25))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v23))))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v3) (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0)
                                             (coe du_σ'8320'_92 (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v28 v29)))))
                                  (coe
                                     d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))
                                     (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v27))
                                        (coe v23))
                                     (coe du_leF_1472 (coe v13) (coe v14)) (coe v19) (coe v8)
                                     (coe v9) (coe v10))
                                  (coe
                                     (\ v28 v29 v30 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_Δ_1468 (coe v4) (coe v13) (coe v14))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe
                                                du_eg_1478 (coe v3) (coe v4) (coe v13) (coe v14)
                                                (coe v25) (coe v23) (coe v27) (coe v20))
                                             (coe v8))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v3) (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0)
                                             (coe du_σ'8320'_92 (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v28) (coe v31))))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_P_1470 (coe v24) (coe v25) (coe v23) (coe v27))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Elaborate.du_copairIR_332
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v24))
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v25))
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v23))))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v29 v31)))
                                          (coe
                                             d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                (coe v13) (coe v14))
                                             (coe v14)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v27))
                                                (coe v23))
                                             (coe du_leG_1474 (coe v13) (coe v14)) (coe v20)
                                             (coe v8) (coe v9) (coe v10))
                                          (coe
                                             (\ v31 v32 v33 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                     (coe
                                                        (\ v34 v35 v36 ->
                                                           case coe v34 of
                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v37
                                                               -> case coe v35 of
                                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v38
                                                                      -> coe
                                                                           MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                           (coe
                                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                              (coe v30 v37 v38 v36))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v37
                                                               -> case coe v35 of
                                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v38
                                                                      -> coe
                                                                           MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                           (coe
                                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                              (coe v33 v37 v38 v36))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v13 v14 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v24 v25
                      -> case coe v23 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                                  (coe
                                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                     (coe v1) (coe du_Δ_1540 (coe v4) (coe v13) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v25))
                                        (coe v26))
                                     (coe
                                        du_ef_1548 (coe v3) (coe v4) (coe v13) (coe v14) (coe v21)
                                        (coe v26) (coe v25) (coe v19))
                                     (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v25))
                                        (coe v26))
                                     (coe v19) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9)))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_Δ_1540 (coe v4) (coe v13) (coe v14))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v27))
                                             (coe
                                                du_eg_1550 (coe v3) (coe v4) (coe v13) (coe v14)
                                                (coe v21) (coe v27) (coe v25) (coe v20))
                                             (coe v8))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v28) (coe v29))))))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                                     (coe v1)
                                     (coe du_P_1542 (coe v21) (coe v26) (coe v27) (coe v25))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v25))
                                        (coe v23))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Elaborate.du_forkIR_344
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v21))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v26))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v27))))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v3) (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0)
                                             (coe du_σ'8320'_92 (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v30 ->
                                                        coe
                                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                          (coe v28 v30)
                                                          (coe
                                                             (\ v31 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v29 v30)
                                                                  (coe
                                                                     (\ v32 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v31)
                                                                             (coe v32))))))))))))
                                  (coe
                                     d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v13)
                                        (coe v14))
                                     (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v25))
                                        (coe v26))
                                     (coe du_leF_1544 (coe v13) (coe v14)) (coe v19) (coe v8)
                                     (coe v9) (coe v10))
                                  (coe
                                     (\ v28 v29 v30 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_Δ_1540 (coe v4) (coe v13) (coe v14))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v27))
                                             (coe
                                                du_eg_1550 (coe v3) (coe v4) (coe v13) (coe v14)
                                                (coe v21) (coe v27) (coe v25) (coe v20))
                                             (coe v8))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v3) (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0)
                                             (coe du_σ'8320'_92 (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v28) (coe v31))))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                             (coe v0) (coe v1)
                                             (coe du_P_1542 (coe v21) (coe v26) (coe v27) (coe v25))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v23))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Elaborate.du_forkIR_344
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v21))
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v26))
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                   (coe v27))))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v32 ->
                                                        coe
                                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                          (coe v29 v32)
                                                          (coe
                                                             (\ v33 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v31 v32)
                                                                  (coe
                                                                     (\ v34 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v33)
                                                                             (coe v34))))))))))
                                          (coe
                                             d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                (coe v13) (coe v14))
                                             (coe v14)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v25))
                                                (coe v27))
                                             (coe du_leG_1546 (coe v13) (coe v14)) (coe v20)
                                             (coe v8) (coe v9) (coe v10))
                                          (coe
                                             (\ v31 v32 v33 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                     (coe
                                                        (\ v34 v35 v36 ->
                                                           coe
                                                             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                                (coe v0) (coe v1)
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                   (coe
                                                                      du_P_1542 (coe v21) (coe v26)
                                                                      (coe v27) (coe v25))
                                                                   (coe v21))
                                                                (coe v26)
                                                                (coe
                                                                   du_L_1552 (coe v21) (coe v26)
                                                                   (coe v27) (coe v25))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v28) (coe v31))
                                                                   (coe v34)))
                                                             (coe v29 v35)
                                                             (coe
                                                                (\ v37 ->
                                                                   coe
                                                                     MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                                     (coe
                                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                                        (coe v0) (coe v1)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                           (coe
                                                                              du_P_1542 (coe v21)
                                                                              (coe v26) (coe v27)
                                                                              (coe v25))
                                                                           (coe v21))
                                                                        (coe v27)
                                                                        (coe
                                                                           du_R_1554 (coe v21)
                                                                           (coe v26) (coe v27)
                                                                           (coe v25))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v28) (coe v31))
                                                                           (coe v34)))
                                                                     (coe
                                                                        (\ v38 ->
                                                                           coe
                                                                             MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v37)
                                                                                (coe v38))))))
                                                             (coe
                                                                (\ v37 ->
                                                                   coe
                                                                     MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                                                                     (coe v32 v35)
                                                                     (coe
                                                                        (\ v38 ->
                                                                           coe
                                                                             MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v37)
                                                                                (coe v38))))))
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                (coe v30 v34 v35 v36))
                                                             (coe
                                                                (\ v37 v38 v39 ->
                                                                   coe
                                                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                                     (coe
                                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                                        (coe v0) (coe v1)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                           (coe
                                                                              du_P_1542 (coe v21)
                                                                              (coe v26) (coe v27)
                                                                              (coe v25))
                                                                           (coe v21))
                                                                        (coe v27)
                                                                        (coe
                                                                           du_R_1554 (coe v21)
                                                                           (coe v26) (coe v27)
                                                                           (coe v25))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v28) (coe v31))
                                                                           (coe v34)))
                                                                     (coe v32 v35)
                                                                     (coe
                                                                        (\ v40 ->
                                                                           coe
                                                                             MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v37)
                                                                                (coe v40))))
                                                                     (coe
                                                                        (\ v40 ->
                                                                           coe
                                                                             MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v38)
                                                                                (coe v40))))
                                                                     (coe
                                                                        MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                        (coe v33 v34 v35 v36))
                                                                     (coe
                                                                        (\ v40 v41 v42 ->
                                                                           coe
                                                                             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v39)
                                                                                (coe
                                                                                   v42)))))))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v19
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v25 v26 v27
                             -> case coe v26 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v28 v29
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                         (coe
                                            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                            (coe v0) (coe v1)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                  (coe v4) (coe v5)))
                                            (coe du_F_1604 (coe v20) (coe v25) (coe v27) (coe v29))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
                                               (coe v3) (coe v4) (coe v5)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                     (coe v20) (coe v25))
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v29))
                                                  (coe v27))
                                               (coe v19))
                                            (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                            (coe v3) (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v20)
                                                  (coe v25))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v29))
                                               (coe v27))
                                            (coe v19) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                                            (coe v9))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                            (coe v0) (coe v1)
                                            (coe du_F_1604 (coe v20) (coe v25) (coe v27) (coe v29))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                  (coe v25)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v29))
                                                  (coe v27)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Elaborate.du_curryIR_356
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe v25))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe v27))))
                                         (coe
                                            (\ v30 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                 (coe
                                                    (\ v31 ->
                                                       coe
                                                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                                                         (coe
                                                            (\ v32 ->
                                                               coe
                                                                 v30
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v31) (coe v32))))))))
                                         (coe
                                            d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v20)
                                                  (coe v25))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v29))
                                               (coe v27))
                                            (coe v19) (coe v8) (coe v9) (coe v10))
                                         (coe
                                            (\ v30 v31 v32 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                 (coe
                                                    (\ v33 v34 v35 ->
                                                       coe
                                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                         (coe
                                                            (\ v36 v37 v38 ->
                                                               coe
                                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                                 (coe
                                                                    v32
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v33) (coe v36))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v34) (coe v37))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v35) (coe v38)))))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v13 v17 v18
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
               -> case coe v19 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v22
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Adequacy.FaithfulLemmas.d_cata'45'body_404
                                  (coe v0) (coe v1) (coe v3) (coe v4) (coe v13) (coe v22) (coe v21)
                                  (coe v24) (coe v17) (coe v18) (coe v8) (coe v9)
                                  (coe
                                     d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                                     (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v22) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v24))
                                        (coe v21))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                        (coe v13))
                                     (coe v18) (coe v8) (coe v9) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v13 v18 v19
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v25 v26
                             -> coe
                                  MAlonzo.Code.Once.Adequacy.FaithfulLemmas.d_ana'45'body_662
                                  (coe v0) (coe v1) (coe v3) (coe v4) (coe v13) (coe v25) (coe v20)
                                  (coe v24) (coe v26) (coe v18) (coe v19) (coe v8) (coe v9)
                                  (coe
                                     d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                                     (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v26)))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v25) (coe v20)))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                        (coe v13))
                                     (coe v19) (coe v8) (coe v9) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v13 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Adequacy.FaithfulLemmas.d_loop'45'body_868
                    (coe v0) (coe v1) (coe v3) (coe v4) (coe v13) (coe v17) (coe v19)
                    (coe v16) (coe v8) (coe v9)
                    (coe
                       d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                       (coe v13)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                          (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v19) (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                          (coe v13))
                       (coe v16) (coe v8) (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceFaithful.ih∘
d_ih'8728'_970 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ih'8728'_970 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         d_faithful_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v6) (coe v7) (coe v9)
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
            (coe v5) (coe v6) (coe v8) (coe v10))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
            (coe v5) (coe v6) (coe v8) (coe v11))
         (coe
            MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v4)
            (coe v5) (coe v6) (coe v8) (coe v12)))
-- Once.Adequacy.SourceFaithful.binop
d_binop_1000 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_binop_1000 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_arith'45'rel_748 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
               (coe v6))))
      (coe v7) (coe v8) (coe v9) (coe v10)
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5))))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
            (coe v4) (coe v5) (coe v7) (coe v11))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
               (coe v6))
            (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
               (coe v5) (coe v6))))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v6))))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
            (coe v4) (coe v6) (coe v8) (coe v12))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
               (coe v6))
            (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
               (coe v5) (coe v6))))
      (coe v13)
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v3) (coe v4) (coe v7) (coe v11) (coe v0)
         (coe du_σ'8320'_92 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
               (coe v6))
            (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
               (coe v5) (coe v6))
            (coe v14)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v3) (coe v4) (coe v8) (coe v12) (coe v0)
         (coe du_σ'8320'_92 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
               (coe v6))
            (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
               (coe v5) (coe v6))
            (coe v14)))
      (coe
         d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
            (coe v6))
         (coe v5) (coe v7)
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
            (coe v5) (coe v6))
         (coe v11) (coe v13) (coe v14) (coe v15))
      (coe
         d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v5)
            (coe v6))
         (coe v6) (coe v8)
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
            (coe v5) (coe v6))
         (coe v12) (coe v13) (coe v14) (coe v15))
-- Once.Adequacy.SourceFaithful.let-body
d_let'45'body_1028 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_let'45'body_1028 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
         (coe
            MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
            (coe
               (\ v16 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                             (coe v5)))
                       (coe v6) (coe du_leB_2442 (coe v5) (coe v6) (coe v9)) (coe v12))
                    (coe v16)))
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5)))))
               (coe v7)
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                     (coe v4) (coe v5) (coe v7) (coe v10))
                  (coe
                     MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5)))
                     (coe v5) (coe du_leA_2440 (coe v5) (coe v6) (coe v9) (coe v15))))
               (coe v12)))
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe v3) (coe v4) (coe v7) (coe v10) (coe v0)
            (coe du_σ'8320'_92 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                     (coe v5)))
               (coe v5)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                  (coe v5)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                     (coe v5))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                        (coe v5)))
                  (coe v15)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                     (coe v6)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                        (coe v5))))
               (coe v13)))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
            (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'42'__24
               (coe du_Δ'8322'_2436 (coe v4) (coe v6)) (coe v7))
            (coe du_Δ'8242'_2438 (coe v4) (coe v6) (coe v7) (coe v9))
            (coe du_bE_2450 (coe v9)))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
            (coe v1) (coe du_Δ'8242'_2438 (coe v4) (coe v6) (coe v7) (coe v9))
            (coe v8)
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
               (coe addInt (coe (1 :: Integer)) (coe v3))
               (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v7))
               (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v6) (coe v8)
               (coe v11)))
         (coe
            (\ v16 ->
               coe
                 MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                 (coe addInt (coe (1 :: Integer)) (coe v3))
                 (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v7))
                 (coe v8) (coe v11) (coe v0) (coe du_σ'8320'_92 (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v9)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                             (coe v5)))
                       (coe v6)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                          (coe v6)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                             (coe v5)))
                       (coe v13))
                    (coe v16))))
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
            (coe
               (\ v16 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                             (coe v5)))
                       (coe v6) (coe du_leB_2442 (coe v5) (coe v6) (coe v9)) (coe v12))
                    (coe v16)))
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5)))))
               (coe v7)
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v4) (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v3)
                     (coe v4) (coe v5) (coe v7) (coe v10))
                  (coe
                     MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5)))
                     (coe v5) (coe du_leA_2440 (coe v5) (coe v6) (coe v9) (coe v15))))
               (coe v12))
            (coe
               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
               (coe v3) (coe v4) (coe v7) (coe v10) (coe v0)
               (coe du_σ'8320'_92 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                        (coe v5)))
                  (coe v5)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                     (coe v5)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                        (coe v5))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5)))
                     (coe v15)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                        (coe v6)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                           (coe v5))))
                  (coe v13)))
            (coe
               d_ih'8728'_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                     (coe v5)))
               (coe v5) (coe v7)
               (coe du_leA_2440 (coe v5) (coe v6) (coe v9) (coe v15)) (coe v10)
               (coe v12) (coe v13) (coe v14))
            (coe
               (\ v16 v17 v18 ->
                  coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v18))))
         (coe
            du_'46'extendedlambda0_2472 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11)
            (coe v12) (coe v13) (coe v14)))
-- Once.Adequacy.SourceFaithful.sigop-value
d_sigop'45'value_1040 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_sigop'45'value_1040 v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7
  = du_sigop'45'value_1040 v0 v1 v5 v6
du_sigop'45'value_1040 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_sigop'45'value_1040 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         du_sigOp'45'rel_150 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v2) (coe v3)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.SourceFaithful.sigop-arr₀
d_sigop'45'arr'8320'_1058 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_sigop'45'arr'8320'_1058 v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9
  = du_sigop'45'arr'8320'_1058 v0 v1 v6 v8
du_sigop'45'arr'8320'_1058 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_sigop'45'arr'8320'_1058 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
         (coe
            du_sigOp'45'rel_150 (coe v0) (coe v1)
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v2) (coe v3)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Adequacy.SourceFaithful.ref-rel
d_ref'45'rel_1070 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ref'45'rel_1070 v0 v1 v2 ~v3 ~v4 v5 v6 ~v7
  = du_ref'45'rel_1070 v0 v1 v2 v5 v6
du_ref'45'rel_1070 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_ref'45'rel_1070 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
         (coe v1) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v3)
         (coe
            MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v3)
            (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v4)))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.SourceFaithful.lift-morph
d_lift'45'morph_1088 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_lift'45'morph_1088 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_lift'45'morph_1088 v0 v1 v2 v6 v7 v9
du_lift'45'morph_1088 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_lift'45'morph_1088 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
              (coe
                 MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
                 (coe v1) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                 (coe v7) (coe v8))))
-- Once.Adequacy.SourceFaithful._.E
d_E_1246 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_E_1246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
  = du_E_1246 v11
du_E_1246 :: AgdaAny -> AgdaAny
du_E_1246 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1284 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_leF_1284 v6 v7
du_leF_1284 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1284 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_1286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leX_1286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_leX_1286 v6 v7
du_leX_1286 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leX_1286 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v1)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v1)))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1310 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_leF_1310 v6 v7
du_leF_1310 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1310 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_1312 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leX_1312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_leX_1312 v6 v7
du_leX_1312 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leX_1312 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_1338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_1338 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_Δ_1338 v4 v5 v6
du_Δ_1338 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_1338 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1340 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1340 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leF_1340 v5 v6
du_leF_1340 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1340 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_1342 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leX_1342 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leX_1342 v5 v6
du_leX_1342 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leX_1342 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
-- Once.Adequacy.SourceFaithful._.inner
d_inner_1344 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_inner_1344 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13
             ~v14 ~v15
  = du_inner_1344 v3 v4 v5 v6 v7 v8 v9 v11 v12
du_inner_1344 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_inner_1344 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
                  (coe v5))
               (coe v7))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)))
               (coe v2) (coe du_leF_1340 (coe v2) (coe v3))))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v3))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
               (coe v1) (coe v3) (coe v4) (coe v8))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)))
               (coe v3) (coe du_leX_1342 (coe v2) (coe v3)))))
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_1408 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_1408 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_Δ_1408 v4 v5 v6
du_Δ_1408 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_1408 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))))
-- Once.Adequacy.SourceFaithful._.P
d_P_1410 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_P_1410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_P_1410 v7 v8 v9 v10
du_P_1410 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_P_1410 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'42'__24
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v2))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v1))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1412 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leF_1412 v5 v6
du_leF_1412 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1412 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
-- Once.Adequacy.SourceFaithful._.leG
d_leG_1414 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leG_1414 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leG_1414 v5 v6
du_leG_1414 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leG_1414 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
-- Once.Adequacy.SourceFaithful._.ef
d_ef_1416 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ef_1416 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
          ~v15
  = du_ef_1416 v3 v4 v5 v6 v8 v9 v10 v11
du_ef_1416 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_1416 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)))
         (coe v2) (coe du_leF_1412 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.eg
d_eg_1418 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eg_1418 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10 ~v11 v12 ~v13 ~v14
          ~v15
  = du_eg_1418 v3 v4 v5 v6 v7 v8 v10 v12
du_eg_1418 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_1418 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)))
         (coe v3) (coe du_leG_1414 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.body
d_body_1420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15
  = du_body_1420 v7 v8 v9
du_body_1420 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_1420 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))))
            (coe MAlonzo.Code.Once.IR.C_fst_42)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))))
                  (coe MAlonzo.Code.Once.IR.C_snd_48)
                  (coe MAlonzo.Code.Once.IR.C_fst_42))
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_1468 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_1468 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_Δ_1468 v4 v5 v6
du_Δ_1468 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_1468 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe v2)))
-- Once.Adequacy.SourceFaithful._.P
d_P_1470 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_P_1470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_P_1470 v7 v8 v9 v10
du_P_1470 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_P_1470 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'42'__24
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v2))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1472 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leF_1472 v5 v6
du_leF_1472 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1472 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_1474 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leG_1474 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leG_1474 v5 v6
du_leG_1474 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leG_1474 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.ef
d_ef_1476 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ef_1476 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 ~v12 ~v13 ~v14
          ~v15
  = du_ef_1476 v3 v4 v5 v6 v7 v9 v10 v11
du_ef_1476 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_1476 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe v3))
         (coe v2) (coe du_leF_1472 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.eg
d_eg_1478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eg_1478 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9 v10 ~v11 v12 ~v13 ~v14
          ~v15
  = du_eg_1478 v3 v4 v5 v6 v8 v9 v10 v12
du_eg_1478 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_1478 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe v3))
         (coe v3) (coe du_leG_1474 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.L
d_L_1480 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_L_1480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_L_1480 v7 v8 v9
du_L_1480 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_L_1480 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
            (coe MAlonzo.Code.Once.IR.C_fst_42)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.SourceFaithful._.R
d_R_1482 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_R_1482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_R_1482 v7 v8 v9
du_R_1482 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_R_1482 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
            (coe MAlonzo.Code.Once.IR.C_snd_48)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.SourceFaithful._.body
d_body_1484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15
  = du_body_1484 v7 v8 v9
du_body_1484 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_1484 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'43'__22
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))))
      (coe
         MAlonzo.Code.Once.IR.C_case_68
         (coe du_L_1480 (coe v0) (coe v1) (coe v2))
         (coe du_R_1482 (coe v0) (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_distribIR_308
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.C__'8667'__24
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
            (coe
               MAlonzo.Code.Once.IRTy.C__'8667'__24
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_1540 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_1540 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_Δ_1540 v4 v5 v6
du_Δ_1540 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_1540 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe v2)))
-- Once.Adequacy.SourceFaithful._.P
d_P_1542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_P_1542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_P_1542 v7 v8 v9 v10
du_P_1542 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_P_1542 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'42'__24
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_1544 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leF_1544 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leF_1544 v5 v6
du_leF_1544 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leF_1544 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_1546 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leG_1546 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leG_1546 v5 v6
du_leG_1546 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leG_1546 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.ef
d_ef_1548 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ef_1548 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
          ~v15
  = du_ef_1548 v3 v4 v5 v6 v7 v8 v10 v11
du_ef_1548 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_1548 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe v3))
         (coe v2) (coe du_leF_1544 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.eg
d_eg_1550 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eg_1550 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 v12 ~v13 ~v14
          ~v15
  = du_eg_1550 v3 v4 v5 v6 v7 v9 v10 v12
du_eg_1550 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_1550 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6))
            (coe v5))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe v3))
         (coe v3) (coe du_leG_1546 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.L
d_L_1552 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_L_1552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_L_1552 v7 v8 v9 v10
du_L_1552 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_L_1552 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                     (coe v2))))
            (coe MAlonzo.Code.Once.IR.C_fst_42)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.SourceFaithful._.R
d_R_1554 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
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
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_R_1554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_R_1554 v7 v8 v9 v10
du_R_1554 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_R_1554 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
                     (coe v1)))
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
            (coe MAlonzo.Code.Once.IR.C_snd_48)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.SourceFaithful._.F
d_F_1604 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_F_1604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14
  = du_F_1604 v6 v7 v8 v10
du_F_1604 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_F_1604 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
      (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
      (coe v2)
-- Once.Adequacy.SourceFaithful._.body
d_body_1606 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14
  = du_body_1606 v6 v7 v8
du_body_1606 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_1606 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
            (coe MAlonzo.Code.Once.IR.C_fst_42)
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
               (coe MAlonzo.Code.Once.IR.C_snd_48)
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe MAlonzo.Code.Once.IR.C_snd_48)))
-- Once.Adequacy.SourceFaithful._.leM
d_leM_1972 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leM_1972 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leM_1972 v3 v6
du_leM_1972 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leM_1972 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1)))
-- Once.Adequacy.SourceFaithful._.Δs
d_Δs_2060 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δs_2060 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18
  = du_Δs_2060 v4 v6 v7 v8
du_Δs_2060 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δs_2060 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
               (coe v3))))
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_2062 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_2062 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18
  = du_Δ_2062 v4 v7 v8
du_Δ_2062 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_2062 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v1)
            (coe v2)))
-- Once.Adequacy.SourceFaithful._.leAll
d_leAll_2064 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leAll_2064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_leAll_2064 v6 v7 v8
du_leAll_2064 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leAll_2064 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leS
d_leS_2066 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leS_2066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15 ~v16 ~v17 ~v18
  = du_leS_2066 v6 v7 v8
du_leS_2066 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leS_2066 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leL
d_leL_2068 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leL_2068 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_leL_2068 v7 v8
du_leL_2068 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leL_2068 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leR
d_leR_2070 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leR_2070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_leR_2070 v7 v8
du_leR_2070 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leR_2070 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.Eall
d_Eall_2072 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_Eall_2072 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 v16 ~v17 ~v18
  = du_Eall_2072 v4 v6 v7 v8 v16
du_Eall_2072 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_Eall_2072 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe du_leAll_2064 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.rAllᴿ
d_rAll'7487'_2074 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rAll'7487'_2074 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18
  = du_rAll'7487'_2074 v4 v6 v7 v8 v18
du_rAll'7487'_2074 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_rAll'7487'_2074 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe du_leAll_2064 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.rAll
d_rAll_2076 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_rAll_2076 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18
  = du_rAll_2076 v4 v6 v7 v8
du_rAll_2076 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_rAll_2076 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe du_leAll_2064 (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.SourceFaithful._.es
d_es_2078 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_es_2078 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 ~v9 ~v10 v11 v12 v13 ~v14
          ~v15 ~v16 ~v17 ~v18
  = du_es_2078 v3 v4 v6 v7 v8 v11 v12 v13
du_es_2078 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_es_2078 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v5) (coe v6))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v3)
               (coe v4)))
         (coe v2) (coe du_leS_2066 (coe v2) (coe v3) (coe v4)))
-- Once.Adequacy.SourceFaithful._.LL
d_LL_2080 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_LL_2080 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 ~v10 v11 ~v12 ~v13 v14
          ~v15 ~v16 ~v17 ~v18
  = du_LL_2080 v3 v4 v5 v7 v8 v9 v11 v14
du_LL_2080 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_LL_2080 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136
               (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v5 v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v5 v3) (coe v2)
         (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v3))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_242 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v3)
                     (coe v4))
                  (coe v3) (coe du_leL_2068 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe MAlonzo.Code.Once.IR.C_snd_48)))
-- Once.Adequacy.SourceFaithful._.RR
d_RR_2082 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_RR_2082 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 v8 ~v9 v10 ~v11 v12 ~v13 ~v14
          v15 ~v16 ~v17 ~v18
  = du_RR_2082 v3 v4 v5 v7 v8 v10 v12 v15
du_RR_2082 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_RR_2082 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136
               (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v5 v4))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v5 v4) (coe v2)
         (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v4))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_242 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v3)
                     (coe v4))
                  (coe v4) (coe du_leR_2070 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe MAlonzo.Code.Once.IR.C_snd_48)))
-- Once.Adequacy.SourceFaithful._.R₀
d_R'8320'_2084 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_R'8320'_2084 = erased
-- Once.Adequacy.SourceFaithful._..extendedlambda0
d_'46'extendedlambda0_2102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'46'extendedlambda0_2102 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21
  = du_'46'extendedlambda0_2102
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16 v17 v18 v19
      v20 v21
du_'46'extendedlambda0_2102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'46'extendedlambda0_2102 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15 v16 v17 v18 v19 v20
  = case coe v18 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
        -> case coe v22 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v23
               -> case coe v19 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v24
                      -> case coe v20 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                     (coe
                                        d_faithful_950 (coe v0) (coe v1) (coe v2)
                                        (coe addInt (coe (1 :: Integer)) (coe v3))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4)
                                           (coe v11))
                                        (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v7)
                                        (coe v5) (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                           (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v7) (coe du_leL_2068 (coe v7) (coe v8))
                                              (coe
                                                 du_Eall_2072 (coe v4) (coe v6) (coe v7) (coe v8)
                                                 (coe v15)))
                                           (coe v23))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                           (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
                                                 (coe v7) (coe v8))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                       (coe v7) (coe v8)))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                    (coe v7) (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                       (coe v7) (coe v8)))
                                                 (coe v16)))
                                           (coe v24))
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132
                                           (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v7) (coe du_leL_2068 (coe v7) (coe v8))
                                              (coe
                                                 du_rAll'7487'_2074 (coe v4) (coe v6) (coe v7)
                                                 (coe v8) (coe v17)))
                                           (coe v26))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
               -> case coe v19 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v24
                      -> case coe v20 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                     (coe
                                        d_faithful_950 (coe v0) (coe v1) (coe v2)
                                        (coe addInt (coe (1 :: Integer)) (coe v3))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4)
                                           (coe v12))
                                        (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v10 v8)
                                        (coe v5) (coe v14)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v8) (coe du_leR_2070 (coe v7) (coe v8))
                                              (coe
                                                 du_Eall_2072 (coe v4) (coe v6) (coe v7) (coe v8)
                                                 (coe v15)))
                                           (coe v23))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v8)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
                                                 (coe v7) (coe v8))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                       (coe v7) (coe v8)))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                    (coe v7) (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                       (coe v7) (coe v8)))
                                                 (coe v16)))
                                           (coe v24))
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                                 (coe v7) (coe v8))
                                              (coe v8) (coe du_leR_2070 (coe v7) (coe v8))
                                              (coe
                                                 du_rAll'7487'_2074 (coe v4) (coe v6) (coe v7)
                                                 (coe v8) (coe v17)))
                                           (coe v26))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceFaithful._.si
d_si_2186 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_si_2186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
  = du_si_2186 v6 v7 v8 v9 v10
du_si_2186 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_si_2186 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v0))
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful._.si
d_si_2214 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_si_2214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13
  = du_si_2214 v6 v7 v8 v9 v10
du_si_2214 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_si_2214 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v0))
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful._.Δ
d_Δ_2434 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ_2434 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15
  = du_Δ_2434 v4 v5 v6 v9
du_Δ_2434 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ_2434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v3)
               (coe v1))))
-- Once.Adequacy.SourceFaithful._.Δ₂
d_Δ'8322'_2436 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ'8322'_2436 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15
  = du_Δ'8322'_2436 v4 v6
du_Δ'8322'_2436 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ'8322'_2436 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v0) (coe v1))
-- Once.Adequacy.SourceFaithful._.Δ′
d_Δ'8242'_2438 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Δ'8242'_2438 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15
  = du_Δ'8242'_2438 v4 v6 v7 v9
du_Δ'8242'_2438 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Δ'8242'_2438 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8638'__136
         (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v0) (coe v2))
         (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v3 v1))
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2440 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leA_2440 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
           ~v14 v15
  = du_leA_2440 v5 v6 v9 v15
du_leA_2440 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leA_2440 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
      (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v2)
         (coe v0))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v2)
            (coe v0)))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v2)
            (coe v0)))
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2442 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
d_leB_2442 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15
  = du_leB_2442 v5 v6 v9
du_leB_2442 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178
du_leB_2442 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v2)
         (coe v0))
-- Once.Adequacy.SourceFaithful._.E2
d_E2_2444 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 -> AgdaAny
d_E2_2444 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
          ~v14 ~v15
  = du_E2_2444 v4 v5 v6 v9 v12
du_E2_2444 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  AgdaAny -> AgdaAny
du_E2_2444 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v3)
            (coe v1)))
      (coe v2) (coe du_leB_2442 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.rB
d_rB_2446 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_rB_2446 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15
  = du_rB_2446 v4 v5 v6 v9
du_rB_2446 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_rB_2446 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v3)
            (coe v1)))
      (coe v2) (coe du_leB_2442 (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.SourceFaithful._.e1′
d_e1'8242'_2448 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_e1'8242'_2448 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 ~v12
                ~v13 ~v14 v15
  = du_e1'8242'_2448 v3 v4 v5 v6 v7 v9 v10 v15
du_e1'8242'_2448 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_e1'8242'_2448 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v0)
         (coe v1) (coe v2) (coe v4) (coe v6))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v5)
               (coe v2)))
         (coe v2) (coe du_leA_2440 (coe v2) (coe v3) (coe v5) (coe v7)))
-- Once.Adequacy.SourceFaithful._.bE
d_bE_2450 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_bE_2450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15
  = du_bE_2450 v9
du_bE_2450 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_bE_2450 v0
  = coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_242 (coe v0)
-- Once.Adequacy.SourceFaithful._.P
d_P_2452 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_P_2452 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11 ~v12 ~v13 ~v14
         v15
  = du_P_2452 v3 v4 v5 v6 v7 v9 v10 v15
du_P_2452 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_P_2452 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
      (coe du_rB_2446 (coe v1) (coe v2) (coe v3) (coe v5))
      (coe
         du_e1'8242'_2448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.SourceFaithful._.R₀
d_R'8320'_2454 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> ()
d_R'8320'_2454 = erased
-- Once.Adequacy.SourceFaithful._..extendedlambda0
d_'46'extendedlambda0_2472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'46'extendedlambda0_2472 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11
                           v12 v13 v14 ~v15 v16 v17 v18
  = du_'46'extendedlambda0_2472
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11 v12 v13 v14 v16 v17 v18
du_'46'extendedlambda0_2472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'46'extendedlambda0_2472 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15 v16
  = case coe v14 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
        -> case coe v16 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                    (coe
                       d_faithful_950 (coe v0) (coe v1) (coe v2)
                       (coe addInt (coe (1 :: Integer)) (coe v3))
                       (coe MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v4) (coe v7))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v6) (coe v8)
                       (coe v10)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v9)
                          (coe du_E2_2444 (coe v4) (coe v5) (coe v6) (coe v9) (coe v11))
                          (coe v18))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v5)))
                             (coe v6)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v5)))
                             (coe v12))
                          (coe v15))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v6)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v5)))
                             (coe v6) (coe du_leB_2442 (coe v5) (coe v6) (coe v9)) (coe v13))
                          (coe v20)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceFaithful.faithful∅
d_faithful'8709'_2530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_faithful'8709'_2530 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v3)
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
         (coe
            d_faithful_950 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
            (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
