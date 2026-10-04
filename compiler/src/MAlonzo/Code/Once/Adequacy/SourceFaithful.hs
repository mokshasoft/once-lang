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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.SourceFaithful.σ₀
d_σ'8320'_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ'8320'_32 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful.proj₁-subst
d_proj'8321''45'subst_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8321''45'subst_78 = erased
-- Once.Adequacy.SourceFaithful.proj₂-subst
d_proj'8322''45'subst_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8322''45'subst_96 = erased
-- Once.Adequacy.SourceFaithful.subst-T-returnT
d_subst'45'T'45'returnT_108 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_108 = erased
-- Once.Adequacy.SourceFaithful.sigop-value
d_sigop'45'value_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'value_120 = erased
-- Once.Adequacy.SourceFaithful.void-bind′
d_void'45'bind'8242'_140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_void'45'bind'8242'_140 = erased
-- Once.Adequacy.SourceFaithful.void-bind
d_void'45'bind_178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_void'45'bind_178 = erased
-- Once.Adequacy.SourceFaithful.pair-subst⁻
d_pair'45'subst'8315'_204 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'subst'8315'_204 = erased
-- Once.Adequacy.SourceFaithful.push⊎₁⁻
d_push'8846''8321''8315'_224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321''8315'_224 = erased
-- Once.Adequacy.SourceFaithful.push⊎₂⁻
d_push'8846''8322''8315'_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322''8315'_242 = erased
-- Once.Adequacy.SourceFaithful.subst-arrowᴰ
d_subst'45'arrow'7472'_266 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'7472'_266 = erased
-- Once.Adequacy.SourceFaithful.distribute-reduce
d_distribute'45'reduce_284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'reduce_284 = erased
-- Once.Adequacy.SourceFaithful.fst-transport
d_fst'45'transport_312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'transport_312 = erased
-- Once.Adequacy.SourceFaithful.snd-transport
d_snd'45'transport_334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'transport_334 = erased
-- Once.Adequacy.SourceFaithful.inl-transport
d_inl'45'transport_356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inl'45'transport_356 = erased
-- Once.Adequacy.SourceFaithful.inr-transport
d_inr'45'transport_378 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inr'45'transport_378 = erased
-- Once.Adequacy.SourceFaithful.pair-transport
d_pair'45'transport_406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'transport_406 = erased
-- Once.Adequacy.SourceFaithful.morphapp-transport
d_morphapp'45'transport_432 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morphapp'45'transport_432 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ
d_ih'7472'_450 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'_450 = erased
-- Once.Adequacy.SourceFaithful.proj-lookup
d_proj'45'lookup_468 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'lookup_468 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-drop
d_restrictEnv'45'drop_504 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'drop_504 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-keep
d_restrictEnv'45'keep_520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'keep_520 = erased
-- Once.Adequacy.SourceFaithful.liftFn-restrictEnv
d_liftFn'45'restrictEnv_534 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'restrictEnv_534 = erased
-- Once.Adequacy.SourceFaithful.liftFn-∘-restrictEnv
d_liftFn'45''8728''45'restrictEnv_660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45''8728''45'restrictEnv_660 = erased
-- Once.Adequacy.SourceFaithful.ihᴰgen
d_ih'7472'gen_690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'gen_690 = erased
-- Once.Adequacy.SourceFaithful.arith-body-II
d_arith'45'body'45'II_720 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'II_720 = erased
-- Once.Adequacy.SourceFaithful._.reassoc
d_reassoc_752 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reassoc_752 = erased
-- Once.Adequacy.SourceFaithful._.step
d_step_768 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step_768 = erased
-- Once.Adequacy.SourceFaithful.arith-body-FF
d_arith'45'body'45'FF_808 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'FF_808 = erased
-- Once.Adequacy.SourceFaithful._.reassoc
d_reassoc_840 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reassoc_840 = erased
-- Once.Adequacy.SourceFaithful._.step
d_step_856 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step_856 = erased
-- Once.Adequacy.SourceFaithful.arith-body-IB
d_arith'45'body'45'IB_896 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'IB_896 = erased
-- Once.Adequacy.SourceFaithful._.reassoc
d_reassoc_928 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reassoc_928 = erased
-- Once.Adequacy.SourceFaithful._.step
d_step_944 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step_944 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-id
d_restrict'7472''45'id_976 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'id_976 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-subst
d_restrict'7472''45'subst_1030 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'subst_1030 = erased
-- Once.Adequacy.SourceFaithful.liftFn-substΦ
d_liftFn'45'substΦ_1058 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'substΦ_1058 = erased
-- Once.Adequacy.SourceFaithful.bindEnv-denote
d_bindEnv'45'denote_1078 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindEnv'45'denote_1078 = erased
-- Once.Adequacy.SourceFaithful.branch-pair
d_branch'45'pair_1126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch'45'pair_1126 = erased
-- Once.Adequacy.SourceFaithful.branchEnv-denote
d_branchEnv'45'denote_1176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branchEnv'45'denote_1176 = erased
-- Once.Adequacy.SourceFaithful.evalᴰ-restrictEnv
d_eval'7472''45'restrictEnv_1210 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'restrictEnv_1210 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ∘
d_ih'7472''8728'_1236 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472''8728'_1236 = erased
-- Once.Adequacy.SourceFaithful.drop-pure
d_drop'45'pure_1258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'pure_1258 = erased
-- Once.Adequacy.SourceFaithful.app-transport
d_app'45'transport_1290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'transport_1290 = erased
-- Once.Adequacy.SourceFaithful.app-transport₀
d_app'45'transport'8320'_1318 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'transport'8320'_1318 = erased
-- Once.Adequacy.SourceFaithful.app-body-Zero
d_app'45'body'45'Zero_1346 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body'45'Zero_1346 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1372 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_1372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_dγ''_1372 v10
du_dγ''_1372 :: AgdaAny -> AgdaAny
du_dγ''_1372 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1376 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1376 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_1382 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_1382 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_1388 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_1388 = erased
-- Once.Adequacy.SourceFaithful.comp-transport
d_comp'45'transport_1456 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'transport_1456 = erased
-- Once.Adequacy.SourceFaithful.comp-body
d_comp'45'body_1488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'body_1488 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1518 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_1518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13
  = du_dγ''_1518 v11
du_dγ''_1518 :: AgdaAny -> AgdaAny
du_dγ''_1518 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1524 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1524 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1538 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1538 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-comp-reduce
d_eval'7472''45'comp'45'reduce_1554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'comp'45'reduce_1554 = erased
-- Once.Adequacy.SourceFaithful.curry-transport
d_curry'45'transport_1630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'transport_1630 = erased
-- Once.Adequacy.SourceFaithful.curry-body
d_curry'45'body_1654 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'body_1654 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_1676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_1676 v8
du_dγ''_1676 :: AgdaAny -> AgdaAny
du_dγ''_1676 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1682 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1682 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-curry-reduce
d_eval'7472''45'curry'45'reduce_1698 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'curry'45'reduce_1698 = erased
-- Once.Adequacy.SourceFaithful.fork-transport
d_fork'45'transport_1764 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fork'45'transport_1764 = erased
-- Once.Adequacy.SourceFaithful.fork-body
d_fork'45'body_1798 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fork'45'body_1798 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1826 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_1826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_dγ''_1826 v10
du_dγ''_1826 :: AgdaAny -> AgdaAny
du_dγ''_1826 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1832 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1832 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1846 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1846 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-fork-reduce
d_eval'7472''45'fork'45'reduce_1866 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'fork'45'reduce_1866 = erased
-- Once.Adequacy.SourceFaithful.copair-transport
d_copair'45'transport_1940 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_copair'45'transport_1940 = erased
-- Once.Adequacy.SourceFaithful.copair-body
d_copair'45'body_1972 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_copair'45'body_1972 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2002 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_2002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13
  = du_dγ''_2002 v11
du_dγ''_2002 :: AgdaAny -> AgdaAny
du_dγ''_2002 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2008 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2008 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_2022 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_2022 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-copair-reduce
d_eval'7472''45'copair'45'reduce_2038 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'copair'45'reduce_2038 = erased
-- Once.Adequacy.SourceFaithful.app-body
d_app'45'body_2094 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body_2094 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_2120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_dγ''_2120 v10
du_dγ''_2120 :: AgdaAny -> AgdaAny
du_dγ''_2120 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2126 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_2136 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_2142 = erased
-- Once.Adequacy.SourceFaithful.app-body-One
d_app'45'body'45'One_2186 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body'45'One_2186 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dγ''_2212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_dγ''_2212 v10
du_dγ''_2212 :: AgdaAny -> AgdaAny
du_dγ''_2212 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2218 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2218 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_2228 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2234 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_2234 = erased
-- Once.Adequacy.SourceFaithful.subst-arrow₀ᴰ
d_subst'45'arrow'8320''7472'_2270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'8320''7472'_2270 = erased
-- Once.Adequacy.SourceFaithful.faithful
d_faithful_2286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful_2286 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2320 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2320 v10
du_dγ''_2320 :: AgdaAny -> AgdaAny
du_dγ''_2320 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2322 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2322 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2322 v2 v3 v4 v6 v7 v9
du_ee_2322 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2322 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2324 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2324 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_eeF_2324 v2 v3 v4 v6 v7 v9
du_eeF_2324 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2324 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6) v2))))
      (coe
         du_ee_2322 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2328 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2338 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2338 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2368 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2368 v10
du_dγ''_2368 :: AgdaAny -> AgdaAny
du_dγ''_2368 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2370 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2370 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2370 v2 v3 v4 v6 v7 v9
du_ee_2370 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2370 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2372 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2372 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_eeF_2372 v2 v3 v4 v6 v7 v9
du_eeF_2372 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6) v2))))
      (coe
         du_ee_2370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2376 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2376 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2386 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2386 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2418 v10
du_dγ''_2418 :: AgdaAny -> AgdaAny
du_dγ''_2418 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2420 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2420 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2420 v2 v3 v4 v6 v7 v9
du_ee_2420 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2420 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2422 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2422 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_eeF_2422 v2 v3 v4 v6 v7 v9
du_eeF_2422 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2422 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6) v2))))
      (coe
         du_ee_2420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2426 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2436 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2436 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2468 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2468 v10
du_dγ''_2468 :: AgdaAny -> AgdaAny
du_dγ''_2468 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2470 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2470 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2470 v2 v3 v4 v6 v7 v9
du_ee_2470 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2470 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2474 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2474 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2506 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2506 v10
du_dγ''_2506 :: AgdaAny -> AgdaAny
du_dγ''_2506 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2508 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2508 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2508 v2 v3 v4 v6 v7 v9
du_ee_2508 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2508 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2512 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2512 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2544 v10
du_dγ''_2544 :: AgdaAny -> AgdaAny
du_dγ''_2544 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2546 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee_2546 v2 v3 v4 v6 v7 v9
du_ee_2546 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2546 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2550 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2550 = erased
-- Once.Adequacy.SourceFaithful._.Ez
d_Ez_2586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Ez_2586 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_Ez_2586 v3 v5 v6 v10
du_Ez_2586 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Ez_2586 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Zero_6) (coe v2)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Zero_6) (coe v2)))
      (coe v3)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2612 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2612 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2612 v5 v6
du_leF_2612 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2612 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2614 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2614 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2614 v5 v6
du_leX_2614 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2614 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
         (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2636 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2636 v5 v6
du_leF_2636 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2636 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2638 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2638 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2638 v5 v6
du_leX_2638 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2638 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
         (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2660 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2660 v4 v5
du_leF_2660 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2660 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2662 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2662 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2662 v4 v5
du_leX_2662 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2662 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
         (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2664 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_2664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_2664 v10
du_dγ''_2664 :: AgdaAny -> AgdaAny
du_dγ''_2664 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.inner
d_inner_2666 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_inner_2666 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inner_2666 v2 v3 v4 v5 v6 v7 v8 v9
du_inner_2666 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_inner_2666 v0 v1 v2 v3 v4 v5 v6 v7
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
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v2))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v5))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
               (coe v2) (coe du_leF_2660 (coe v2) (coe v3))))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v3))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
               (coe v1) (coe v3) (coe v4) (coe v7))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
               (coe v3) (coe du_leX_2662 (coe v2) (coe v3)))))
-- Once.Adequacy.SourceFaithful._.body
d_body_2668 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_body_2668 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_body_2668 v2 v3 v4 v5 v6 v7 v8 v9
du_body_2668 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_2668 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))))))
      (coe
         du_inner_2666 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Adequacy.SourceFaithful._.liftFn-curry-reduce-effApp
d_liftFn'45'curry'45'reduce'45'effApp_2672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'curry'45'reduce'45'effApp_2672 = erased
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2732 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2732 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_2732 v4 v5
du_leF_2732 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2732 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
-- Once.Adequacy.SourceFaithful._.leG
d_leG_2734 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_2734 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_2734 v4 v5
du_leG_2734 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_2734 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
         (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v0)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2772 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_2772 v4 v5
du_leF_2772 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2772 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_2774 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_2774 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_2774 v4 v5
du_leG_2774 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_2774 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2800 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2800 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_2800 v4 v5
du_leF_2800 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2800 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_2802 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_2802 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_2802 v4 v5
du_leG_2802 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_2802 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2876 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2876 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2876 v4 v5
du_leA_2876 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2876 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2878 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2878 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2878 v4 v5
du_leB_2878 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2878 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2896 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2896 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2896 v4 v5
du_leA_2896 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2896 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2898 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2898 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2898 v4 v5
du_leB_2898 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2898 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2916 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2916 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2916 v4 v5
du_leA_2916 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2916 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2918 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2918 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2918 v4 v5
du_leB_2918 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2918 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2936 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2936 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2936 v4 v5
du_leA_2936 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2936 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2938 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2938 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2938 v4 v5
du_leB_2938 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2938 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2956 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2956 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2956 v4 v5
du_leA_2956 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2956 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2958 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2958 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2958 v4 v5
du_leB_2958 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2958 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2976 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2976 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2976 v4 v5
du_leA_2976 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2976 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2978 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2978 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2978 v4 v5
du_leB_2978 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2978 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_2996 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_2996 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_2996 v4 v5
du_leA_2996 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_2996 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_2998 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_2998 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_2998 v4 v5
du_leB_2998 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_2998 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3024 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3024 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3024 v4 v5
du_leA_3024 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3024 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3026 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3026 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3026 v4 v5
du_leB_3026 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3026 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3044 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3044 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3044 v4 v5
du_leA_3044 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3044 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3046 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3046 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3046 v4 v5
du_leB_3046 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3046 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3064 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3064 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3064 v4 v5
du_leA_3064 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3064 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3066 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3066 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3066 v4 v5
du_leB_3066 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3066 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3084 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3084 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3084 v4 v5
du_leA_3084 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3084 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3086 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3086 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3086 v4 v5
du_leB_3086 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3086 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3104 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3104 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3104 v4 v5
du_leA_3104 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3104 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3106 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3106 v4 v5
du_leB_3106 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3106 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3124 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3124 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3124 v4 v5
du_leA_3124 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3124 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3126 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3126 v4 v5
du_leB_3126 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3126 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3144 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3144 v4 v5
du_leA_3144 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3144 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3146 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3146 v4 v5
du_leB_3146 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3146 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3164 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leA_3164 v4 v5
du_leA_3164 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3164 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3166 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3166 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 = du_leB_3166 v4 v5
du_leB_3166 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3166 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3196 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3196 v4 v5
du_leA_3196 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3196 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3198 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3198 v4 v5
du_leB_3198 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3198 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leM
d_leM_3244 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leM_3244 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_leM_3244 v2 v5
du_leM_3244 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leM_3244 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
         (coe v1))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3292 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3292 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3292 v5 v6
du_leA_3292 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3292 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
         (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0)))
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3294 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3294 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3294 v5 v6
du_leB_3294 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3294 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_3296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_3296 v10
du_dγ''_3296 :: AgdaAny -> AgdaAny
du_dγ''_3296 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3298 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E2''_3298 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_E2''_3298 v3 v5 v6 v10
du_E2''_3298 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3298 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v2) (coe du_leB_3294 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3300 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee1_3300 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10
  = du_ee1_3300 v2 v3 v5 v6 v7 v8
du_ee1_3300 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3300 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
         (coe v1) (coe v2) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_One_8) (coe v2)))
         (coe v2) (coe du_leA_3292 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3302 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee2_3302 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee2_3302 v2 v3 v4 v6 v7 v9
du_ee2_3302 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3302 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v3)
      (coe v2) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_let'45'reduce_3306 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3320 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e2'45'eq_3320 = erased
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3356 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3356 v5 v6
du_leA_3356 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3356 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
         (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0)))
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3358 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3358 v5 v6
du_leB_3358 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3358 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3360 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_3360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_dγ''_3360 v10
du_dγ''_3360 :: AgdaAny -> AgdaAny
du_dγ''_3360 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E2''_3362 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_E2''_3362 v3 v5 v6 v10
du_E2''_3362 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3362 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v2) (coe du_leB_3358 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3364 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee1_3364 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 ~v10
  = du_ee1_3364 v2 v3 v5 v6 v7 v8
du_ee1_3364 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3364 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
         (coe v1) (coe v2) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2)))
         (coe v2) (coe du_leA_3356 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3366 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_ee2_3366 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10
  = du_ee2_3366 v2 v3 v4 v6 v7 v9
du_ee2_3366 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3366 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v3)
      (coe v2) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3370 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_let'45'reduce_3370 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3384 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e2'45'eq_3384 = erased
-- Once.Adequacy.SourceFaithful._.leAll
d_leAll_3570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leAll_3570 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15
  = du_leAll_3570 v5 v6 v7
du_leAll_3570 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leAll_3570 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leS
d_leS_3572 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leS_3572 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15
  = du_leS_3572 v5 v6 v7
du_leS_3572 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leS_3572 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leL
d_leL_3574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leL_3574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leL_3574 v6 v7
du_leL_3574 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leL_3574 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leR
d_leR_3576 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leR_3576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leR_3576 v6 v7
du_leR_3576 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leR_3576 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.Eall
d_Eall_3578 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Eall_3578 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 v15
  = du_Eall_3578 v3 v5 v6 v7 v15
du_Eall_3578 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall_3578 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe du_leAll_3570 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.Eₗ
d_E'8343'_3580 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'8343'_3580 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 v15
  = du_E'8343'_3580 v3 v5 v6 v7 v15
du_E'8343'_3580 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8343'_3580 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v2) (coe du_leL_3574 (coe v2) (coe v3))
      (coe du_Eall_3578 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.Eᵣ
d_E'7523'_3582 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_E'7523'_3582 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 v15
  = du_E'7523'_3582 v3 v5 v6 v7 v15
du_E'7523'_3582 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'7523'_3582 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v3) (coe du_leR_3576 (coe v2) (coe v3))
      (coe du_Eall_3578 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3584 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_dγ''_3584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 v15
  = du_dγ''_3584 v15
du_dγ''_3584 :: AgdaAny -> AgdaAny
du_dγ''_3584 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.Eall'
d_Eall''_3586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Eall''_3586 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
              ~v13 ~v14 v15
  = du_Eall''_3586 v3 v5 v6 v7 v15
du_Eall''_3586 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall''_3586 v0 v1 v2 v3 v4
  = coe du_Eall_3578 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful._.es
d_es_3588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_es_3588 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 v10 v11 v12 ~v13 ~v14
          ~v15
  = du_es_3588 v2 v3 v5 v6 v7 v10 v11 v12
du_es_3588 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_es_3588 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
         (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v5) (coe v6))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
               (coe v4)))
         (coe v2) (coe du_leS_3572 (coe v2) (coe v3) (coe v4)))
-- Once.Adequacy.SourceFaithful._.LL
d_LL_3590 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_LL_3590 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8 ~v9 v10 ~v11 ~v12 v13 ~v14
          ~v15
  = du_LL_3590 v2 v3 v4 v6 v7 v8 v10 v13
du_LL_3590 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_LL_3590 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v3))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v3)
         (coe v2) (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v3))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_242 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                     (coe v4))
                  (coe v3) (coe du_leL_3574 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe MAlonzo.Code.Once.IR.C_snd_48)))
-- Once.Adequacy.SourceFaithful._.RR
d_RR_3592 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_RR_3592 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 v11 ~v12 ~v13 v14
          ~v15
  = du_RR_3592 v2 v3 v4 v6 v7 v9 v11 v14
du_RR_3592 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_RR_3592 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v4))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v4)
         (coe v2) (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v4))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_242 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                     (coe v4))
                  (coe v4) (coe du_leR_3576 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe MAlonzo.Code.Once.IR.C_snd_48)))
-- Once.Adequacy.SourceFaithful._.reshape
d_reshape_3594 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_reshape_3594 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 ~v14 v15 v16
  = du_reshape_3594 v3 v5 v6 v7 v15 v16
du_reshape_3594 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_reshape_3594 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_3586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_3586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      v5
-- Once.Adequacy.SourceFaithful._.branchᴰ
d_branch'7472'_3602 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_branch'7472'_3602 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 v13
                    v14 v15
  = du_branch'7472'_3602
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15
du_branch'7472'_3602 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_branch'7472'_3602 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v15 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
           (coe v0) (coe v1)
           (coe
              MAlonzo.Code.Once.IRTy.C__'42'__20
              (coe
                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v6)
                          (coe v7)))))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10)))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
           (coe
              du_LL_3590 (coe v2) (coe v3) (coe v4) (coe v6) (coe v7) (coe v8)
              (coe v10) (coe v12))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_3586 (coe v3) (coe v5) (coe v6) (coe v7) (coe v14))
              (coe v15)))
      (\ v15 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
           (coe v0) (coe v1)
           (coe
              MAlonzo.Code.Once.IRTy.C__'42'__20
              (coe
                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v6)
                          (coe v7)))))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v11)))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
           (coe
              du_RR_3592 (coe v2) (coe v3) (coe v4) (coe v6) (coe v7) (coe v9)
              (coe v11) (coe v13))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_3586 (coe v3) (coe v5) (coe v6) (coe v7) (coe v14))
              (coe v15)))
-- Once.Adequacy.SourceFaithful._.dd-reduce
d_dd'45'reduce_3612 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dd'45'reduce_3612 = erased
-- Once.Adequacy.SourceFaithful._.case-fuse
d_case'45'fuse_3626 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'fuse_3626 = erased
-- Once.Adequacy.SourceFaithful._.assoc-fuse
d_assoc'45'fuse_3636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc'45'fuse_3636 = erased
-- Once.Adequacy.SourceFaithful._.case-reduce
d_case'45'reduce_3644 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'reduce_3644 = erased
-- Once.Adequacy.SourceFaithful._.LL-lift
d_LL'45'lift_3650 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LL'45'lift_3650 = erased
-- Once.Adequacy.SourceFaithful._.RR-lift
d_RR'45'lift_3660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RR'45'lift_3660 = erased
-- Once.Adequacy.SourceFaithful._.branch-eq
d_branch'45'eq_3674 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch'45'eq_3674 = erased
-- Once.Adequacy.SourceFaithful.faithful∅
d_faithful'8709'_3720 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful'8709'_3720 = erased
