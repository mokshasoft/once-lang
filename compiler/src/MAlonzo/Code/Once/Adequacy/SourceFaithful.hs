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
d_inj'45'uu_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'45'uu_60 = erased
-- Once.Adequacy.SourceFaithful.proj₁-subst
d_proj'8321''45'subst_76 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8321''45'subst_76 = erased
-- Once.Adequacy.SourceFaithful.proj₂-subst
d_proj'8322''45'subst_94 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8322''45'subst_94 = erased
-- Once.Adequacy.SourceFaithful.subst-T-returnT
d_subst'45'T'45'returnT_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_106 = erased
-- Once.Adequacy.SourceFaithful.subst-T-apply
d_subst'45'T'45'apply_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'apply_120 = erased
-- Once.Adequacy.SourceFaithful.pair-subst⁻
d_pair'45'subst'8315'_142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'subst'8315'_142 = erased
-- Once.Adequacy.SourceFaithful.push⊎₁⁻
d_push'8846''8321''8315'_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321''8315'_162 = erased
-- Once.Adequacy.SourceFaithful.push⊎₂⁻
d_push'8846''8322''8315'_180 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322''8315'_180 = erased
-- Once.Adequacy.SourceFaithful.subst-arrowᴰ
d_subst'45'arrow'7472'_204 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'7472'_204 = erased
-- Once.Adequacy.SourceFaithful.distribute-reduce
d_distribute'45'reduce_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'reduce_222 = erased
-- Once.Adequacy.SourceFaithful.fst-transport
d_fst'45'transport_252 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'transport_252 = erased
-- Once.Adequacy.SourceFaithful.snd-transport
d_snd'45'transport_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'transport_278 = erased
-- Once.Adequacy.SourceFaithful.inl-transport
d_inl'45'transport_304 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inl'45'transport_304 = erased
-- Once.Adequacy.SourceFaithful.inr-transport
d_inr'45'transport_330 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inr'45'transport_330 = erased
-- Once.Adequacy.SourceFaithful.pair-transport
d_pair'45'transport_362 ::
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
d_pair'45'transport_362 = erased
-- Once.Adequacy.SourceFaithful.morphapp-transport
d_morphapp'45'transport_392 ::
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
d_morphapp'45'transport_392 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ
d_ih'7472'_414 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'_414 = erased
-- Once.Adequacy.SourceFaithful.sigop-value
d_sigop'45'value_434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'value_434 = erased
-- Once.Adequacy.SourceFaithful.proj-lookup
d_proj'45'lookup_454 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'lookup_454 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-drop
d_restrictEnv'45'drop_498 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'drop_498 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-keep
d_restrictEnv'45'keep_516 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'keep_516 = erased
-- Once.Adequacy.SourceFaithful.liftFn-restrictEnv
d_liftFn'45'restrictEnv_532 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'restrictEnv_532 = erased
-- Once.Adequacy.SourceFaithful.liftFn-∘-restrictEnv
d_liftFn'45''8728''45'restrictEnv_678 ::
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
d_liftFn'45''8728''45'restrictEnv_678 = erased
-- Once.Adequacy.SourceFaithful.restrictEnv-trace
d_restrictEnv'45'trace_714 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrictEnv'45'trace_714 = erased
-- Once.Adequacy.SourceFaithful.ihᴰgen
d_ih'7472'gen_804 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'gen_804 = erased
-- Once.Adequacy.SourceFaithful.inject-BB
d_inject'45'BB_818 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'45'BB_818 = erased
-- Once.Adequacy.SourceFaithful.arith-body-II
d_arith'45'body'45'II_848 ::
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
d_arith'45'body'45'II_848 = erased
-- Once.Adequacy.SourceFaithful.arith-body-FF
d_arith'45'body'45'FF_912 ::
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
d_arith'45'body'45'FF_912 = erased
-- Once.Adequacy.SourceFaithful.arith-body-IB
d_arith'45'body'45'IB_976 ::
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
d_arith'45'body'45'IB_976 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-id
d_restrict'7472''45'id_1026 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'id_1026 = erased
-- Once.Adequacy.SourceFaithful.restrictᴰ-subst
d_restrict'7472''45'subst_1080 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_restrict'7472''45'subst_1080 = erased
-- Once.Adequacy.SourceFaithful.liftFn-substΦ
d_liftFn'45'substΦ_1110 ::
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
d_liftFn'45'substΦ_1110 = erased
-- Once.Adequacy.SourceFaithful.bindEnv-denote
d_bindEnv'45'denote_1134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindEnv'45'denote_1134 = erased
-- Once.Adequacy.SourceFaithful.branch-pair
d_branch'45'pair_1190 ::
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
d_branch'45'pair_1190 = erased
-- Once.Adequacy.SourceFaithful.branchEnv-denote
d_branchEnv'45'denote_1244 ::
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
d_branchEnv'45'denote_1244 = erased
-- Once.Adequacy.SourceFaithful.evalᴰ-restrictEnv
d_eval'7472''45'restrictEnv_1280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'restrictEnv_1280 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ∘
d_ih'7472''8728'_1308 ::
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
d_ih'7472''8728'_1308 = erased
-- Once.Adequacy.SourceFaithful.app-trace
d_app'45'trace_1334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'trace_1334 = erased
-- Once.Adequacy.SourceFaithful.case-trace
d_case'45'trace_1350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'trace_1350 = erased
-- Once.Adequacy.SourceFaithful.comp-trace
d_comp'45'trace_1362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'trace_1362 = erased
-- Once.Adequacy.SourceFaithful.drop-pure
d_drop'45'pure_1374 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'pure_1374 = erased
-- Once.Adequacy.SourceFaithful.app-transport
d_app'45'transport_1408 ::
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
d_app'45'transport_1408 = erased
-- Once.Adequacy.SourceFaithful.app-transport₀
d_app'45'transport'8320'_1440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'transport'8320'_1440 = erased
-- Once.Adequacy.SourceFaithful.app-body-Zero
d_app'45'body'45'Zero_1476 ::
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
d_app'45'body'45'Zero_1476 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1504 ::
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
d_dγ''_1504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_1504 v9
du_dγ''_1504 :: AgdaAny -> AgdaAny
du_dγ''_1504 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1508 ::
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
d_ihf'45'T_1508 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_1514 ::
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
d_ihx'45'T_1514 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_1520 ::
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
d_eval'7472''45'app'45'reduce_1520 = erased
-- Once.Adequacy.SourceFaithful.comp-transport
d_comp'45'transport_1594 ::
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
d_comp'45'transport_1594 = erased
-- Once.Adequacy.SourceFaithful.comp-body
d_comp'45'body_1634 ::
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
d_comp'45'body_1634 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1666 ::
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
d_dγ''_1666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13
  = du_dγ''_1666 v10
du_dγ''_1666 :: AgdaAny -> AgdaAny
du_dγ''_1666 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1672 ::
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
d_ihf'45'T_1672 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1686 ::
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
d_ihg'45'T_1686 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-comp-reduce
d_eval'7472''45'comp'45'reduce_1702 ::
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
d_eval'7472''45'comp'45'reduce_1702 = erased
-- Once.Adequacy.SourceFaithful.curry-transport
d_curry'45'transport_1770 ::
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
d_curry'45'transport_1770 = erased
-- Once.Adequacy.SourceFaithful.curry-body
d_curry'45'body_1800 ::
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
d_curry'45'body_1800 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1824 ::
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
d_dγ''_1824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_dγ''_1824 v7
du_dγ''_1824 :: AgdaAny -> AgdaAny
du_dγ''_1824 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1830 ::
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
d_ihf'45'T_1830 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-curry-reduce
d_eval'7472''45'curry'45'reduce_1846 ::
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
d_eval'7472''45'curry'45'reduce_1846 = erased
-- Once.Adequacy.SourceFaithful.fork-transport
d_fork'45'transport_1914 ::
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
d_fork'45'transport_1914 = erased
-- Once.Adequacy.SourceFaithful.fork-body
d_fork'45'body_1956 ::
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
d_fork'45'body_1956 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1986 ::
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
d_dγ''_1986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_1986 v9
du_dγ''_1986 :: AgdaAny -> AgdaAny
du_dγ''_1986 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1992 ::
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
d_ihf'45'T_1992 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_2006 ::
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
d_ihg'45'T_2006 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-fork-reduce
d_eval'7472''45'fork'45'reduce_2026 ::
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
d_eval'7472''45'fork'45'reduce_2026 = erased
-- Once.Adequacy.SourceFaithful.copair-transport
d_copair'45'transport_2098 ::
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
d_copair'45'transport_2098 = erased
-- Once.Adequacy.SourceFaithful.copair-body
d_copair'45'body_2138 ::
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
d_copair'45'body_2138 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2170 ::
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
d_dγ''_2170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13
  = du_dγ''_2170 v10
du_dγ''_2170 :: AgdaAny -> AgdaAny
du_dγ''_2170 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2176 ::
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
d_ihf'45'T_2176 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_2190 ::
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
d_ihg'45'T_2190 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-copair-reduce
d_eval'7472''45'copair'45'reduce_2206 ::
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
d_eval'7472''45'copair'45'reduce_2206 = erased
-- Once.Adequacy.SourceFaithful._.branch
d_branch_2218 ::
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
d_branch_2218 = erased
-- Once.Adequacy.SourceFaithful.app-body
d_app'45'body_2274 ::
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
d_app'45'body_2274 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2302 ::
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
d_dγ''_2302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_2302 v9
du_dγ''_2302 :: AgdaAny -> AgdaAny
du_dγ''_2302 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2308 ::
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
d_ihf'45'T_2308 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2318 ::
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
d_ihx'45'T_2318 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2324 ::
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
d_eval'7472''45'app'45'reduce_2324 = erased
-- Once.Adequacy.SourceFaithful.app-body-One
d_app'45'body'45'One_2378 ::
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
d_app'45'body'45'One_2378 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2406 ::
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
d_dγ''_2406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_dγ''_2406 v9
du_dγ''_2406 :: AgdaAny -> AgdaAny
du_dγ''_2406 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_2412 ::
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
d_ihf'45'T_2412 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_2422 ::
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
d_ihx'45'T_2422 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_2428 ::
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
d_eval'7472''45'app'45'reduce_2428 = erased
-- Once.Adequacy.SourceFaithful.subst-arrow₀ᴰ
d_subst'45'arrow'8320''7472'_2468 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'8320''7472'_2468 = erased
-- Once.Adequacy.SourceFaithful.faithful
d_faithful_2486 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful_2486 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2520 v8
du_dγ''_2520 :: AgdaAny -> AgdaAny
du_dγ''_2520 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2522 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2522 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2522 v1 v2 v3 v4 v5 v7
du_ee_2522 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2522 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2524 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2524 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2524 v1 v2 v3 v4 v5 v7
du_eeF_2524 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2524 v0 v1 v2 v3 v4 v5
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
         du_ee_2522 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2530 ::
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
d_drop_2530 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2542 ::
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
d_red_2542 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2578 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2578 v8
du_dγ''_2578 :: AgdaAny -> AgdaAny
du_dγ''_2578 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2580 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2580 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2580 v1 v2 v3 v4 v5 v7
du_ee_2580 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2580 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2582 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2582 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2582 v1 v2 v3 v4 v5 v7
du_eeF_2582 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2582 v0 v1 v2 v3 v4 v5
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
         du_ee_2580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2588 ::
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
d_drop_2588 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2600 ::
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
d_red_2600 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2638 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2638 v8
du_dγ''_2638 :: AgdaAny -> AgdaAny
du_dγ''_2638 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2640 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2640 v1 v2 v3 v4 v5 v7
du_ee_2640 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2640 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.eeF
d_eeF_2642 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_eeF_2642 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_eeF_2642 v1 v2 v3 v4 v5 v7
du_eeF_2642 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eeF_2642 v0 v1 v2 v3 v4 v5
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
         du_ee_2640 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.drop
d_drop_2648 ::
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
d_drop_2648 = erased
-- Once.Adequacy.SourceFaithful._.red
d_red_2660 ::
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
d_red_2660 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2698 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2698 v8
du_dγ''_2698 :: AgdaAny -> AgdaAny
du_dγ''_2698 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2700 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2700 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2700 v1 v2 v3 v4 v5 v7
du_ee_2700 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2700 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2704 ::
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
d_red_2704 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2742 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2742 v8
du_dγ''_2742 :: AgdaAny -> AgdaAny
du_dγ''_2742 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2744 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2744 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2744 v1 v2 v3 v4 v5 v7
du_ee_2744 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2744 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2748 ::
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
d_red_2748 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2786 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_dγ''_2786 v8
du_dγ''_2786 :: AgdaAny -> AgdaAny
du_dγ''_2786 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_2788 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_2788 ~v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_ee_2788 v1 v2 v3 v4 v5 v7
du_ee_2788 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_2788 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v2)
      (coe v4) (coe v5)
-- Once.Adequacy.SourceFaithful._.red
d_red_2792 ::
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
d_red_2792 = erased
-- Once.Adequacy.SourceFaithful._.Ez
d_Ez_2834 ::
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
d_Ez_2834 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_Ez_2834 v2 v4 v5 v9
du_Ez_2834 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Ez_2834 v0 v1 v2 v3
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
d_leF_2866 ::
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
d_leF_2866 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2866 v4 v5
du_leF_2866 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2866 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2868 ::
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
d_leX_2868 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2868 v4 v5
du_leX_2868 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2868 v0 v1
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
d_leF_2896 ::
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
d_leF_2896 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2896 v4 v5
du_leF_2896 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2896 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1))
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2898 ::
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
d_leX_2898 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2898 v4 v5
du_leX_2898 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2898 v0 v1
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
d_leF_2926 ::
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
d_leF_2926 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leF_2926 v3 v4
du_leF_2926 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_2926 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leX
d_leX_2928 ::
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
d_leX_2928 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leX_2928 v3 v4
du_leX_2928 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leX_2928 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2930 ::
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
d_dγ''_2930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_2930 v9
du_dγ''_2930 :: AgdaAny -> AgdaAny
du_dγ''_2930 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.inner
d_inner_2932 ::
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
d_inner_2932 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_inner_2932 v1 v2 v3 v4 v5 v6 v7 v8
du_inner_2932 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_inner_2932 v0 v1 v2 v3 v4 v5 v6 v7
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
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v5))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe v3))
               (coe v2) (coe du_leF_2926 (coe v2) (coe v3))))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                     (coe v3))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370 (coe v0)
               (coe v1) (coe v3) (coe v4) (coe v7))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
                  (coe v3))
               (coe v3) (coe du_leX_2928 (coe v2) (coe v3)))))
-- Once.Adequacy.SourceFaithful._.body
d_body_2934 ::
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
d_body_2934 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_body_2934 v1 v2 v3 v4 v5 v6 v7 v8
du_body_2934 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_2934 v0 v1 v2 v3 v4 v5 v6 v7
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
         du_inner_2932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.liftFn-curry-reduce-effApp
d_liftFn'45'curry'45'reduce'45'effApp_2938 ::
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
d_liftFn'45'curry'45'reduce'45'effApp_2938 = erased
-- Once.Adequacy.SourceFaithful._.leF
d_leF_3012 ::
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
d_leF_3012 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_3012 v3 v4
du_leF_3012 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_3012 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_3014 ::
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
d_leG_3014 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_3014 v3 v4
du_leG_3014 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_3014 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_3062 ::
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
d_leF_3062 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_3062 v3 v4
du_leF_3062 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_3062 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_3064 ::
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
d_leG_3064 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_3064 v3 v4
du_leG_3064 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_3064 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leF
d_leF_3096 ::
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
d_leF_3096 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leF_3096 v3 v4
du_leF_3096 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leF_3096 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leG
d_leG_3098 ::
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
d_leG_3098 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_leG_3098 v3 v4
du_leG_3098 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leG_3098 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3194 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3194 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3194 v3 v4
du_leA_3194 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3194 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3196 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3196 v3 v4
du_leB_3196 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3196 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3222 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3222 v3 v4
du_leA_3222 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3222 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3224 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3224 v3 v4
du_leB_3224 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3224 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3250 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3250 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3250 v3 v4
du_leA_3250 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3250 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3252 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3252 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3252 v3 v4
du_leB_3252 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3252 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3278 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3278 v3 v4
du_leA_3278 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3278 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3280 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3280 v3 v4
du_leB_3280 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3280 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3306 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3306 v3 v4
du_leA_3306 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3306 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3308 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3308 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3308 v3 v4
du_leB_3308 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3308 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3334 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3334 v3 v4
du_leA_3334 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3334 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3336 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3336 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3336 v3 v4
du_leB_3336 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3336 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3362 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3362 v3 v4
du_leA_3362 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3362 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3364 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3364 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3364 v3 v4
du_leB_3364 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3364 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3402 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3402 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3402 v3 v4
du_leA_3402 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3402 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3404 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3404 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3404 v3 v4
du_leB_3404 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3404 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3430 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3430 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3430 v3 v4
du_leA_3430 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3430 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3432 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3432 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3432 v3 v4
du_leB_3432 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3432 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3458 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3458 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3458 v3 v4
du_leA_3458 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3458 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3460 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3460 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3460 v3 v4
du_leB_3460 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3460 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3486 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3486 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3486 v3 v4
du_leA_3486 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3486 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3488 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3488 v3 v4
du_leB_3488 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3488 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3514 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3514 v3 v4
du_leA_3514 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3514 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3516 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3516 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3516 v3 v4
du_leB_3516 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3516 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3542 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3542 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3542 v3 v4
du_leA_3542 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3542 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3544 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3544 v3 v4
du_leB_3544 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3544 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3570 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3570 v3 v4
du_leA_3570 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3570 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3572 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3572 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3572 v3 v4
du_leB_3572 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3572 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3598 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leA_3598 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leA_3598 v3 v4
du_leA_3598 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3598 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3600 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
d_leB_3600 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_leB_3600 v3 v4
du_leB_3600 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3600 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3642 ::
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
d_leA_3642 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3642 v3 v4
du_leA_3642 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3642 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leB
d_leB_3644 ::
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
d_leB_3644 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3644 v3 v4
du_leB_3644 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3644 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leM
d_leM_3700 ::
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
d_leM_3700 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leM_3700 v1 v4
du_leM_3700 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leM_3700 v0 v1
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
d_leA_3754 ::
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
d_leA_3754 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3754 v4 v5
du_leA_3754 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3754 v0 v1
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
d_leB_3756 ::
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
d_leB_3756 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3756 v4 v5
du_leB_3756 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3756 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3758 ::
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
d_dγ''_3758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_3758 v9
du_dγ''_3758 :: AgdaAny -> AgdaAny
du_dγ''_3758 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3760 ::
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
d_E2''_3760 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_E2''_3760 v2 v4 v5 v9
du_E2''_3760 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3760 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v1)))
      (coe v2) (coe du_leB_3756 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3762 ::
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
d_ee1_3762 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_ee1_3762 v1 v2 v4 v5 v6 v7
du_ee1_3762 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3762 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370 (coe v0)
         (coe v1) (coe v2) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_One_8) (coe v2)))
         (coe v2) (coe du_leA_3754 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3764 ::
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
d_ee2_3764 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_ee2_3764 v1 v2 v3 v5 v6 v8
du_ee2_3764 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3764 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_One_8) v3)
      (coe v2) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3768 ::
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
d_let'45'reduce_3768 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3784 ::
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
d_e2'45'eq_3784 = erased
-- Once.Adequacy.SourceFaithful._.leA
d_leA_3826 ::
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
d_leA_3826 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leA_3826 v4 v5
du_leA_3826 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leA_3826 v0 v1
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
d_leB_3828 ::
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
d_leB_3828 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_leB_3828 v4 v5
du_leB_3828 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leB_3828 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v0))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_3830 ::
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
d_dγ''_3830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_3830 v9
du_dγ''_3830 :: AgdaAny -> AgdaAny
du_dγ''_3830 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.E2'
d_E2''_3832 ::
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
d_E2''_3832 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_E2''_3832 v2 v4 v5 v9
du_E2''_3832 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E2''_3832 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v1)))
      (coe v2) (coe du_leB_3828 (coe v1) (coe v2)) (coe v3)
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_3834 ::
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
d_ee1_3834 ~v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_ee1_3834 v1 v2 v4 v5 v6 v7
du_ee1_3834 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_3834 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370 (coe v0)
         (coe v1) (coe v2) (coe v4) (coe v5))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v3)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2)))
         (coe v2) (coe du_leA_3826 (coe v2) (coe v3)))
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_3836 ::
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
d_ee2_3836 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_ee2_3836 v1 v2 v3 v5 v6 v8
du_ee2_3836 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_3836 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'8759'__66
         (coe MAlonzo.Code.Once.Type.C_Many_10) v3)
      (coe v2) (coe v5)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_3840 ::
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
d_let'45'reduce_3840 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_3856 ::
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
d_e2'45'eq_3856 = erased
-- Once.Adequacy.SourceFaithful._.leAll
d_leAll_4092 ::
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
d_leAll_4092 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15
  = du_leAll_4092 v4 v5 v6
du_leAll_4092 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leAll_4092 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leS
d_leS_4094 ::
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
d_leS_4094 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
           ~v14 ~v15
  = du_leS_4094 v4 v5 v6
du_leS_4094 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leS_4094 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
      (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v1)
         (coe v2))
-- Once.Adequacy.SourceFaithful._.leL
d_leL_4096 ::
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
d_leL_4096 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leL_4096 v5 v6
du_leL_4096 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leL_4096 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.leR
d_leR_4098 ::
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
d_leR_4098 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15
  = du_leR_4098 v5 v6
du_leR_4098 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276
du_leR_4098 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
      (coe v0) (coe v1)
-- Once.Adequacy.SourceFaithful._.Eall
d_Eall_4100 ::
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
d_Eall_4100 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            v14 ~v15
  = du_Eall_4100 v2 v4 v5 v6 v14
du_Eall_4100 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall_4100 v0 v1 v2 v3 v4
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
      (coe du_leAll_4092 (coe v1) (coe v2) (coe v3)) (coe v4)
-- Once.Adequacy.SourceFaithful._.Eₗ
d_E'8343'_4102 ::
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
d_E'8343'_4102 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15
  = du_E'8343'_4102 v2 v4 v5 v6 v14
du_E'8343'_4102 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'8343'_4102 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v2) (coe du_leL_4096 (coe v2) (coe v3))
      (coe du_Eall_4100 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.Eᵣ
d_E'7523'_4104 ::
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
d_E'7523'_4104 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15
  = du_E'7523'_4104 v2 v4 v5 v6 v14
du_E'7523'_4104 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_E'7523'_4104 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v2)
         (coe v3))
      (coe v3) (coe du_leR_4098 (coe v2) (coe v3))
      (coe du_Eall_4100 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_4106 ::
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
d_dγ''_4106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15
  = du_dγ''_4106 v14
du_dγ''_4106 :: AgdaAny -> AgdaAny
du_dγ''_4106 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.Eall'
d_Eall''_4108 ::
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
d_Eall''_4108 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              ~v13 v14 ~v15
  = du_Eall''_4108 v2 v4 v5 v6 v14
du_Eall''_4108 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 -> AgdaAny -> AgdaAny
du_Eall''_4108 v0 v1 v2 v3 v4
  = coe du_Eall_4100 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.SourceFaithful._.es
d_es_4110 ::
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
d_es_4110 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11 ~v12 ~v13 ~v14
          ~v15
  = du_es_4110 v1 v2 v4 v5 v6 v9 v10 v11
du_es_4110 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_es_4110 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370 (coe v0)
         (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v5) (coe v6))
         (coe v7))
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_90 (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v2)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v3)
               (coe v4)))
         (coe v2) (coe du_leS_4094 (coe v2) (coe v3) (coe v4)))
-- Once.Adequacy.SourceFaithful._.LL
d_LL_4112 ::
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
d_LL_4112 ~v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 v9 ~v10 ~v11 v12 ~v13 ~v14
          ~v15
  = du_LL_4112 v1 v2 v3 v5 v6 v7 v9 v12
du_LL_4112 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_LL_4112 v0 v1 v2 v3 v4 v5 v6 v7
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
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v3)
         (coe v2) (coe v7))
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
                  (coe v3) (coe du_leL_4096 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_44))
            (coe MAlonzo.Code.Once.IR.C_snd_50)))
-- Once.Adequacy.SourceFaithful._.RR
d_RR_4114 ::
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
d_RR_4114 ~v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 v10 ~v11 ~v12 v13 ~v14
          ~v15
  = du_RR_4114 v1 v2 v3 v5 v6 v8 v10 v13
du_RR_4114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_RR_4114 v0 v1 v2 v3 v4 v5 v6 v7
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
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_370
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v6))
         (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v5 v4)
         (coe v2) (coe v7))
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
                  (coe v4) (coe du_leR_4098 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IR.C_fst_44))
            (coe MAlonzo.Code.Once.IR.C_snd_50)))
-- Once.Adequacy.SourceFaithful._.reshape
d_reshape_4116 ::
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
d_reshape_4116 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 ~v15 v16
  = du_reshape_4116 v2 v4 v5 v6 v14 v16
du_reshape_4116 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_reshape_4116 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4108 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      (\ v6 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4108 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
              (coe v6)))
      v5
-- Once.Adequacy.SourceFaithful._.branchᴰ
d_branch'7472'_4124 ::
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
d_branch'7472'_4124 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                    v14 ~v15
  = du_branch'7472'_4124
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_branch'7472'_4124 ::
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
du_branch'7472'_4124 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
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
              du_LL_4112 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7)
              (coe v9) (coe v11))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4108 (coe v2) (coe v4) (coe v5) (coe v6) (coe v13))
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
              du_RR_4114 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v8)
              (coe v10) (coe v12))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe du_Eall''_4108 (coe v2) (coe v4) (coe v5) (coe v6) (coe v13))
              (coe v14)))
-- Once.Adequacy.SourceFaithful._.dd-reduce
d_dd'45'reduce_4134 ::
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
d_dd'45'reduce_4134 = erased
-- Once.Adequacy.SourceFaithful._.case-fuse
d_case'45'fuse_4150 ::
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
d_case'45'fuse_4150 = erased
-- Once.Adequacy.SourceFaithful._.assoc-fuse
d_assoc'45'fuse_4160 ::
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
d_assoc'45'fuse_4160 = erased
-- Once.Adequacy.SourceFaithful._.case-reduce
d_case'45'reduce_4170 ::
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
d_case'45'reduce_4170 = erased
-- Once.Adequacy.SourceFaithful._.LL-lift
d_LL'45'lift_4178 ::
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
d_LL'45'lift_4178 = erased
-- Once.Adequacy.SourceFaithful._.RR-lift
d_RR'45'lift_4192 ::
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
d_RR'45'lift_4192 = erased
-- Once.Adequacy.SourceFaithful._.branch-eq
d_branch'45'eq_4208 ::
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
d_branch'45'eq_4208 = erased
-- Once.Adequacy.SourceFaithful.faithful∅
d_faithful'8709'_4262 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful'8709'_4262 = erased
