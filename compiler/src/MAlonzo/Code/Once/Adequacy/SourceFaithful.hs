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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.SourceFaithful.inj-uu
d_inj'45'uu_54 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'45'uu_54 = erased
-- Once.Adequacy.SourceFaithful.proj₁-subst
d_proj'8321''45'subst_70 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8321''45'subst_70 = erased
-- Once.Adequacy.SourceFaithful.proj₂-subst
d_proj'8322''45'subst_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8322''45'subst_88 = erased
-- Once.Adequacy.SourceFaithful.subst-T-returnT
d_subst'45'T'45'returnT_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_100 = erased
-- Once.Adequacy.SourceFaithful.subst-T-apply
d_subst'45'T'45'apply_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'apply_114 = erased
-- Once.Adequacy.SourceFaithful.pair-subst⁻
d_pair'45'subst'8315'_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'subst'8315'_136 = erased
-- Once.Adequacy.SourceFaithful.push⊎₁⁻
d_push'8846''8321''8315'_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321''8315'_156 = erased
-- Once.Adequacy.SourceFaithful.push⊎₂⁻
d_push'8846''8322''8315'_174 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322''8315'_174 = erased
-- Once.Adequacy.SourceFaithful.subst-arrowᴰ
d_subst'45'arrow'7472'_198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'7472'_198 = erased
-- Once.Adequacy.SourceFaithful.distribute-reduce
d_distribute'45'reduce_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'reduce_216 = erased
-- Once.Adequacy.SourceFaithful.fst-transport
d_fst'45'transport_246 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'transport_246 = erased
-- Once.Adequacy.SourceFaithful.snd-transport
d_snd'45'transport_272 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'transport_272 = erased
-- Once.Adequacy.SourceFaithful.inl-transport
d_inl'45'transport_298 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inl'45'transport_298 = erased
-- Once.Adequacy.SourceFaithful.inr-transport
d_inr'45'transport_324 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inr'45'transport_324 = erased
-- Once.Adequacy.SourceFaithful.pair-transport
d_pair'45'transport_356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'transport_356 = erased
-- Once.Adequacy.SourceFaithful.morphapp-transport
d_morphapp'45'transport_386 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morphapp'45'transport_386 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ
d_ih'7472'_408 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'_408 = erased
-- Once.Adequacy.SourceFaithful.sigop-value
d_sigop'45'value_428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'value_428 = erased
-- Once.Adequacy.SourceFaithful.proj-lookup
d_proj'45'lookup_448 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'lookup_448 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-drop
d_restrictEnv'45'drop_492 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'drop_492 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-keep
d_restrictEnv'45'keep_510 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'keep_510 = erased
-- Once.Adequacy.SourceFaithful.liftFn-restrictEnv
d_liftFn'45'restrictEnv_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'restrictEnv_526 = erased
-- Once.Adequacy.SourceFaithful.liftFn-∘-restrictEnv
d_liftFn'45''8728''45'restrictEnv_672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45''8728''45'restrictEnv_672 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-trace
d_restrictEnv'45'trace_708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'trace_708 = erased
-- Once.Adequacy.SourceFaithful.ihᴰgen
d_ih'7472'gen_798 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'gen_798 = erased
-- Once.Adequacy.SourceFaithful.inject-BB
d_inject'45'BB_812 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'45'BB_812 = erased
-- Once.Adequacy.SourceFaithful.arith-body-II
d_arith'45'body'45'II_842 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'II_842 = erased
-- Once.Adequacy.SourceFaithful.arith-body-FF
d_arith'45'body'45'FF_906 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'FF_906 = erased
-- Once.Adequacy.SourceFaithful.arith-body-IB
d_arith'45'body'45'IB_970 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arith'45'body'45'IB_970 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-id
d_restrict'7472''45'id_1020 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'id_1020 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-subst
d_restrict'7472''45'subst_1074 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'subst_1074 = erased
-- Once.Adequacy.SourceFaithful.liftFn-substΦ
d_liftFn'45'substΦ_1104 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'substΦ_1104 = erased
-- Once.Adequacy.SourceFaithful.bindEnv-denote
d_bindEnv'45'denote_1128 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindEnv'45'denote_1128 = erased
-- Once.Adequacy.SourceFaithful.branch-pair
d_branch'45'pair_1184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch'45'pair_1184 = erased
-- Once.Adequacy.SourceFaithful.branchEnv-denote
d_branchEnv'45'denote_1238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branchEnv'45'denote_1238 = erased
-- Once.Adequacy.SourceFaithful.evalᴰ-restrictEnv
d_eval'7472''45'restrictEnv_1274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'restrictEnv_1274 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ∘
d_ih'7472''8728'_1302 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472''8728'_1302 = erased
-- Once.Adequacy.SourceFaithful.app-trace
d_app'45'trace_1328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'trace_1328 = erased
-- Once.Adequacy.SourceFaithful.case-trace
d_case'45'trace_1344 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'trace_1344 = erased
-- Once.Adequacy.SourceFaithful.comp-trace
d_comp'45'trace_1356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'trace_1356 = erased
-- Once.Adequacy.SourceFaithful.app-transport
d_app'45'transport_1394 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'transport_1394 = erased
-- Once.Adequacy.SourceFaithful.app-transport₀
d_app'45'transport'8320'_1426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'transport'8320'_1426 = erased
-- Once.Adequacy.SourceFaithful.app-body-Zero
d_app'45'body'45'Zero_1462 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body'45'Zero_1462 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1490 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_1490 v9
du_dγ''_1490 :: AgdaAny -> AgdaAny
du_dγ''_1490 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1494 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1494 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_1500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_1500 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_1506 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_1506 = erased
-- Once.Adequacy.SourceFaithful.comp-transport
d_comp'45'transport_1568 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'transport_1568 = erased
-- Once.Adequacy.SourceFaithful.comp-body
d_comp'45'body_1608 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'body_1608 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13
  = du_dγ''_1640 v10
du_dγ''_1640 :: AgdaAny -> AgdaAny
du_dγ''_1640 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1646 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1646 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1660 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-comp-reduce
d_eval'7472''45'comp'45'reduce_1676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'comp'45'reduce_1676 = erased
-- Once.Adequacy.SourceFaithful.curry-transport
d_curry'45'transport_1742 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'transport_1742 = erased
-- Once.Adequacy.SourceFaithful.curry-body
d_curry'45'body_1772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'body_1772 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1796 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_dγ''_1796 v7
du_dγ''_1796 :: AgdaAny -> AgdaAny
du_dγ''_1796 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1802 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1802 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-curry-reduce
d_eval'7472''45'curry'45'reduce_1818 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'curry'45'reduce_1818 = erased
-- Once.Adequacy.SourceFaithful.fork-transport
d_fork'45'transport_1886 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fork'45'transport_1886 = erased
-- Once.Adequacy.SourceFaithful.fork-body
d_fork'45'body_1928 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fork'45'body_1928 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1958 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_1958 v9
du_dγ''_1958 :: AgdaAny -> AgdaAny
du_dγ''_1958 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1964 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1964 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1978 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1978 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-fork-reduce
d_eval'7472''45'fork'45'reduce_1998 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'fork'45'reduce_1998 = erased
-- Once.Adequacy.SourceFaithful.copair-transport
d_copair'45'transport_2070 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_copair'45'transport_2070 = erased
-- Once.Adequacy.SourceFaithful.copair-body
d_copair'45'body_2110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_copair'45'body_2110 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_2142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13
  = du_dγ''_2142 v10
du_dγ''_2142 :: AgdaAny -> AgdaAny
du_dγ''_2142 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2148 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_2162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_2162 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-copair-reduce
d_eval'7472''45'copair'45'reduce_2178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'copair'45'reduce_2178 = erased
-- Once.Adequacy.SourceFaithful._.branch
d_branch_2190 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch_2190 = erased
-- Once.Adequacy.SourceFaithful.app-body
d_app'45'body_2246 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body_2246 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_2274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_2274 v9
du_dγ''_2274 :: AgdaAny -> AgdaAny
du_dγ''_2274 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2280 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_2290 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_2296 = erased
-- Once.Adequacy.SourceFaithful.app-body-One
d_app'45'body'45'One_2338 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body'45'One_2338 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2366 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_2366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_2366 v9
du_dγ''_2366 :: AgdaAny -> AgdaAny
du_dγ''_2366 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2372 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_2372 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2382 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_2382 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2388 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_2388 = erased
-- Once.Adequacy.SourceFaithful.subst-arrow₀ᴰ
d_subst'45'arrow'8320''7472'_2416 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'8320''7472'_2416 = erased
-- Once.Adequacy.SourceFaithful.faithful
d_faithful_2434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful_2434 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2468 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2468 v8
du_dγ''_2468 :: AgdaAny -> AgdaAny
du_dγ''_2468 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2470 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2470 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2470 v1 v2 v3 v4 v5 v7
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
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2472 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2472 v1 v2 v3 v4 v5 v7
du_eeF_2472 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2472 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
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
         du_ee_2470 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2478 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2478 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2490 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2490 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2526 v8
du_dγ''_2526 :: AgdaAny -> AgdaAny
du_dγ''_2526 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2528 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2528 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2528 v1 v2 v3 v4 v5 v7
du_ee_2528 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2528 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2530 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2530 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2530 v1 v2 v3 v4 v5 v7
du_eeF_2530 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2530 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
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
         du_ee_2528 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2536 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2536 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2548 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2586 v8
du_dγ''_2586 :: AgdaAny -> AgdaAny
du_dγ''_2586 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2588 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2588 v1 v2 v3 v4 v5 v7
du_ee_2588 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2588 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2590 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2590 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2590 v1 v2 v3 v4 v5 v7
du_eeF_2590 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2590 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
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
         du_ee_2588 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop_2596 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2608 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2608 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2646 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2646 v8
du_dγ''_2646 :: AgdaAny -> AgdaAny
du_dγ''_2646 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2648 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2648 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2648 v1 v2 v3 v4 v5 v7
du_ee_2648 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2648 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2652 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2652 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2690 v8
du_dγ''_2690 :: AgdaAny -> AgdaAny
du_dγ''_2690 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2692 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2692 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2692 v1 v2 v3 v4 v5 v7
du_ee_2692 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2692 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2696 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2696 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2734 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2734 v8
du_dγ''_2734 :: AgdaAny -> AgdaAny
du_dγ''_2734 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2736 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2736 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2736 v1 v2 v3 v4 v5 v7
du_ee_2736 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2736 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v2)
      (coe v4) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2740 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_red_2740 = erased
-- Once.Adequacy.SourceFaithful._.Ez
d_Ez_2782 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_Ez_2782 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_Ez_2782 v2 v4 v5 v9
du_Ez_2782 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Ez_2782 v0 v1 v2 v3
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
d_leF_2814 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2814 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2814 v4 v5
du_leF_2814 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2814 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2816 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2816 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2816 v4 v5
du_leX_2816 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2816 v0 v1
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
d_leF_2844 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2844 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2844 v4 v5
du_leF_2844 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2844 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2846 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2846 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2846 v4 v5
du_leX_2846 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2846 v0 v1
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
d_leF_2874 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2874 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2874 v3 v4
du_leF_2874 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2874 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2876 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leX_2876 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2876 v3 v4
du_leX_2876 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2876 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2878 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_2878 v9
du_dγ''_2878 :: AgdaAny -> AgdaAny
du_dγ''_2878 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.inner
d_inner_2880 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_inner_2880 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_inner_2880 v1 v2 v3 v4 v5 v6 v7 v8
du_inner_2880 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_inner_2880 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v4))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v5)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v4)))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v2))))
            (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
               (coe v0) (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v5))
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v6))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe v3))
               (coe v2) (coe du_leF_2874 (coe v2) (coe v3))))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v3))))
            (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
               (coe v0) (coe v1) (coe v3) (coe v4)
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v7))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe v3))
               (coe v3) (coe du_leX_2876 (coe v2) (coe v3)))))
-- Once.Adequacy.SourceFaithful._.body
d_body_2882 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_body_2882 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_body_2882 v1 v2 v3 v4 v5 v6 v7 v8
du_body_2882 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_2882 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe v3)))))
      (coe
         du_inner_2880 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.liftFn-curry-reduce-effApp
d_liftFn'45'curry'45'reduce'45'effApp_2886 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'curry'45'reduce'45'effApp_2886 = erased
-- Once.Adequacy.SourceFaithful._.leF
d_leF_2960 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_2960 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_2960 v3 v4
du_leF_2960 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2960 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_2962 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_2962 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_2962 v3 v4
du_leG_2962 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_2962 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_3010 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_3010 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_leF_3010 v3 v4
du_leF_3010 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_3010 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_3012 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_3012 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_leG_3012 v3 v4
du_leG_3012 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_3012 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_3044 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leF_3044 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_3044 v3 v4
du_leF_3044 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_3044 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_3046 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leG_3046 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_3046 v3 v4
du_leG_3046 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_3046 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3142 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3142 v3 v4
du_leA_3142 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3142 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3144 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3144 v3 v4
du_leB_3144 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3144 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3170 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3170 v3 v4
du_leA_3170 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3170 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3172 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3172 v3 v4
du_leB_3172 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3172 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3198 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3198 v3 v4
du_leA_3198 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3198 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3200 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3200 v3 v4
du_leB_3200 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3200 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3226 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3226 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3226 v3 v4
du_leA_3226 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3226 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3228 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3228 v3 v4
du_leB_3228 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3228 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3254 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3254 v3 v4
du_leA_3254 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3254 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3256 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3256 v3 v4
du_leB_3256 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3256 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3282 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3282 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3282 v3 v4
du_leA_3282 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3282 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3284 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3284 v3 v4
du_leB_3284 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3284 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3310 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3310 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3310 v3 v4
du_leA_3310 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3310 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3312 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3312 v3 v4
du_leB_3312 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3312 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3350 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3350 v3 v4
du_leA_3350 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3350 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3352 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3352 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3352 v3 v4
du_leB_3352 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3352 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3378 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3378 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3378 v3 v4
du_leA_3378 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3378 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3380 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3380 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3380 v3 v4
du_leB_3380 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3380 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3406 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3406 v3 v4
du_leA_3406 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3406 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3408 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3408 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3408 v3 v4
du_leB_3408 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3408 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3434 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3434 v3 v4
du_leA_3434 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3434 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3436 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3436 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3436 v3 v4
du_leB_3436 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3436 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3462 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3462 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3462 v3 v4
du_leA_3462 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3462 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3464 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3464 v3 v4
du_leB_3464 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3464 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3490 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3490 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3490 v3 v4
du_leA_3490 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3490 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3492 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3492 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3492 v3 v4
du_leB_3492 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3492 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3518 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3518 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3518 v3 v4
du_leA_3518 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3518 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3520 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3520 v3 v4
du_leB_3520 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3520 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3546 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3546 v3 v4
du_leA_3546 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3546 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3548 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3548 v3 v4
du_leB_3548 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3548 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3590 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3590 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3590 v3 v4
du_leA_3590 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3590 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3592 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3592 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3592 v3 v4
du_leB_3592 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3592 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leM
d_leM_3648 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leM_3648 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leM_3648 v1 v4
du_leM_3648 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leM_3648 v0 v1
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
d_leA_3702 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3702 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3702 v4 v5
du_leA_3702 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3702 v0 v1
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
d_leB_3704 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3704 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3704 v4 v5
du_leB_3704 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3704 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3706 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_3706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_3706 v9
du_dγ''_3706 :: AgdaAny -> AgdaAny
du_dγ''_3706 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E2''_3708 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_E2''_3708 v2 v4 v5 v9
du_E2''_3708 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3708 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v2) (coe du_leB_3704 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3710 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee1_3710 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_ee1_3710 v1 v2 v4 v5 v6 v7
du_ee1_3710 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3710 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_One_8) (coe v2)))
         (coe v2) (coe du_leA_3702 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3712 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee2_3712 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_ee2_3712 v1 v2 v3 v5 v6 v8
du_ee2_3712 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3712 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v3)
      (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3716 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_let'45'reduce_3716 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3726 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e2'45'eq_3726 = erased
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3768 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3768 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3768 v4 v5
du_leA_3768 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3768 v0 v1
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
d_leB_3770 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3770 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3770 v4 v5
du_leB_3770 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3770 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_3772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_3772 v9
du_dγ''_3772 :: AgdaAny -> AgdaAny
du_dγ''_3772 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3774 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_E2''_3774 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_E2''_3774 v2 v4 v5 v9
du_E2''_3774 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3774 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v2) (coe du_leB_3770 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3776 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee1_3776 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_ee1_3776 v1 v2 v4 v5 v6 v7
du_ee1_3776 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3776 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
         (coe v0) (coe v1) (coe v2) (coe v4)
         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2)))
         (coe v2) (coe du_leA_3768 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3778 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee2_3778 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_ee2_3778 v1 v2 v3 v5 v6 v8
du_ee2_3778 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3778 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v3)
      (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3782 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_let'45'reduce_3782 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3792 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e2'45'eq_3792 = erased
-- Once.Adequacy.SourceFaithful._.leAll
d_leAll_4028 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leAll_4028 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15
  = du_leAll_4028 v4 v5 v6
du_leAll_4028 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leAll_4028 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leS
d_leS_4030 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leS_4030 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15
  = du_leS_4030 v4 v5 v6
du_leS_4030 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leS_4030 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leL
d_leL_4032 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leL_4032 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leL_4032 v5 v6
du_leL_4032 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leL_4032 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leR
d_leR_4034 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leR_4034 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leR_4034 v5 v6
du_leR_4034 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leR_4034 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.Eall
d_Eall_4036 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> AgdaAny
d_Eall_4036 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            v14 ~v15
  = du_Eall_4036 v2 v4 v5 v6 v14
du_Eall_4036 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall_4036 v0 v1 v2 v3 v4
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
      (coe du_leAll_4028 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.Eₗ
d_E'8343'_4038 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> AgdaAny
d_E'8343'_4038 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15
  = du_E'8343'_4038 v2 v4 v5 v6 v14
du_E'8343'_4038 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8343'_4038 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v2) (coe du_leL_4032 (coe v2) (coe v3))
      (coe du_Eall_4036 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.Eᵣ
d_E'7523'_4040 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> AgdaAny
d_E'7523'_4040 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15
  = du_E'7523'_4040 v2 v4 v5 v6 v14
du_E'7523'_4040 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'7523'_4040 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v3) (coe du_leR_4034 (coe v2) (coe v3))
      (coe du_Eall_4036 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_4042 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> AgdaAny
d_dγ''_4042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15
  = du_dγ''_4042 v14
du_dγ''_4042 :: AgdaAny -> AgdaAny
du_dγ''_4042 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.Eall'
d_Eall''_4044 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> AgdaAny
d_Eall''_4044 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              ~v13 v14 ~v15
  = du_Eall''_4044 v2 v4 v5 v6 v14
du_Eall''_4044 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall''_4044 v0 v1 v2 v3 v4
  = coe du_Eall_4036 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful._.es
d_es_4046 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_es_4046 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11 ~v12 ~v13 ~v14
          ~v15
  = du_es_4046 v1 v2 v4 v5 v6 v9 v10 v11
du_es_4046 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_es_4046 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
         (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v5) (coe v6))
         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
               (coe v4)))
         (coe v2) (coe du_leS_4030 (coe v2) (coe v3) (coe v4)))
-- Once.Adequacy.SourceFaithful._.LL
d_LL_4048 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_LL_4048 ~v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 v9 ~v10 ~v11 v12 ~v13 ~v14
          ~v15
  = du_LL_4048 v1 v2 v3 v5 v6 v7 v9 v12
du_LL_4048 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_LL_4048 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v3))))
      (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v3)
         (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v3))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_228 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                     (coe v4))
                  (coe v3) (coe du_leL_4032 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_44))
            (coe MAlonzo.Code.Once.IR.C_snd_50)))
-- Once.Adequacy.SourceFaithful._.RR
d_RR_4050 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_RR_4050 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 v10 ~v11 ~v12 v13 ~v14
          ~v15
  = du_RR_4050 v1 v2 v3 v5 v6 v8 v10 v13
du_RR_4050 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_RR_4050 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v4))))
      (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_370
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v4)
         (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v7))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v4))))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v6)))
         (coe MAlonzo.Code.Once.Surface.Elaborate.du_bindEnv_228 (coe v5))
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                           (coe v4)))))
               (coe
                  MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
                     (coe v4))
                  (coe v4) (coe du_leR_4034 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_44))
            (coe MAlonzo.Code.Once.IR.C_snd_50)))
-- Once.Adequacy.SourceFaithful._.reshape
d_reshape_4052 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_reshape_4052 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15 v16
  = du_reshape_4052 v2 v4 v5 v6 v14 v16
du_reshape_4052 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_reshape_4052 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4044 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4044 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      v5
-- Once.Adequacy.SourceFaithful._.branchᴰ
d_branch'7472'_4060 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'7472'_4060 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                    v14 ~v15
  = du_branch'7472'_4060
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_branch'7472'_4060 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'7472'_4060 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v14 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
           (coe v0)
           (coe
              MAlonzo.Code.Once.IRTy.C__'42'__20
              (coe
                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v5)
                          (coe v6)))))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9)))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
           (coe
              du_LL_4048 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
              (coe v9) (coe v11))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4044 (coe v2) (coe v4) (coe v5) (coe v6) (coe v13))
              (coe v14)))
      (\ v14 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
           (coe v0)
           (coe
              MAlonzo.Code.Once.IRTy.C__'42'__20
              (coe
                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v5)
                          (coe v6)))))
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10)))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
           (coe
              du_RR_4050 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v8)
              (coe v10) (coe v12))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4044 (coe v2) (coe v4) (coe v5) (coe v6) (coe v13))
              (coe v14)))
-- Once.Adequacy.SourceFaithful._.dd-reduce
d_dd'45'reduce_4070 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dd'45'reduce_4070 = erased
-- Once.Adequacy.SourceFaithful._.case-fuse
d_case'45'fuse_4084 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'fuse_4084 = erased
-- Once.Adequacy.SourceFaithful._.assoc-fuse
d_assoc'45'fuse_4094 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc'45'fuse_4094 = erased
-- Once.Adequacy.SourceFaithful._.case-reduce
d_case'45'reduce_4106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'reduce_4106 = erased
-- Once.Adequacy.SourceFaithful._.LL-lift
d_LL'45'lift_4114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_LL'45'lift_4114 = erased
-- Once.Adequacy.SourceFaithful._.RR-lift
d_RR'45'lift_4128 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RR'45'lift_4128 = erased
-- Once.Adequacy.SourceFaithful._.branch-eq
d_branch'45'eq_4144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
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
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch'45'eq_4144 = erased
-- Once.Adequacy.SourceFaithful.faithful∅
d_faithful'8709'_4198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful'8709'_4198 = erased
