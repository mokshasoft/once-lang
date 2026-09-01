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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
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
d_inj'45'uu_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'45'uu_40 = erased
-- Once.Adequacy.SourceFaithful.proj₁-subst
d_proj'8321''45'subst_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8321''45'subst_56 = erased
-- Once.Adequacy.SourceFaithful.proj₂-subst
d_proj'8322''45'subst_74 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'8322''45'subst_74 = erased
-- Once.Adequacy.SourceFaithful.subst-T-returnT
d_subst'45'T'45'returnT_86 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_86 = erased
-- Once.Adequacy.SourceFaithful.subst-T-apply
d_subst'45'T'45'apply_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'apply_100 = erased
-- Once.Adequacy.SourceFaithful.pair-subst⁻
d_pair'45'subst'8315'_122 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'subst'8315'_122 = erased
-- Once.Adequacy.SourceFaithful.push⊎₁⁻
d_push'8846''8321''8315'_142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321''8315'_142 = erased
-- Once.Adequacy.SourceFaithful.push⊎₂⁻
d_push'8846''8322''8315'_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322''8315'_160 = erased
-- Once.Adequacy.SourceFaithful.subst-arrowᴰ
d_subst'45'arrow'7472'_184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow'7472'_184 = erased
-- Once.Adequacy.SourceFaithful.distribute-reduce
d_distribute'45'reduce_202 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distribute'45'reduce_202 = erased
-- Once.Adequacy.SourceFaithful.fst-transport
d_fst'45'transport_232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'transport_232 = erased
-- Once.Adequacy.SourceFaithful.snd-transport
d_snd'45'transport_258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'transport_258 = erased
-- Once.Adequacy.SourceFaithful.inl-transport
d_inl'45'transport_284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inl'45'transport_284 = erased
-- Once.Adequacy.SourceFaithful.inr-transport
d_inr'45'transport_310 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inr'45'transport_310 = erased
-- Once.Adequacy.SourceFaithful.pair-transport
d_pair'45'transport_342 ::
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
d_pair'45'transport_342 = erased
-- Once.Adequacy.SourceFaithful.morphapp-transport
d_morphapp'45'transport_372 ::
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
d_morphapp'45'transport_372 = erased
-- Once.Adequacy.SourceFaithful.ihᴰ
d_ih'7472'_394 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'7472'_394 = erased
-- Once.Adequacy.SourceFaithful.sigop-value
d_sigop'45'value_416 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'value_416 = erased
-- Once.Adequacy.SourceFaithful.proj-lookup
d_proj'45'lookup_436 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_proj'45'lookup_436 = erased
-- Once.Adequacy.SourceFaithful.app-trace
d_app'45'trace_472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'trace_472 = erased
-- Once.Adequacy.SourceFaithful.case-trace
d_case'45'trace_488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'trace_488 = erased
-- Once.Adequacy.SourceFaithful.comp-trace
d_comp'45'trace_500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'trace_500 = erased
-- Once.Adequacy.SourceFaithful.app-transport
d_app'45'transport_538 ::
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
d_app'45'transport_538 = erased
-- Once.Adequacy.SourceFaithful.comp-transport
d_comp'45'transport_594 ::
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
d_comp'45'transport_594 = erased
-- Once.Adequacy.SourceFaithful.comp-body
d_comp'45'body_636 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp'45'body_636 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_664 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
           ~v13 ~v14
  = du_dγ''_664 v11
du_dγ''_664 :: AgdaAny -> AgdaAny
du_dγ''_664 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ef
d_ef_666 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ef_666 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_ef_666 v2 v6 v7 v8 v9
du_ef_666 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_666 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.eg
d_eg_668 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eg_668 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14
  = du_eg_668 v2 v5 v6 v8 v10
du_eg_668 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_668 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_674 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_674 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_688 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_688 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-comp-reduce
d_eval'7472''45'comp'45'reduce_704 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'comp'45'reduce_704 = erased
-- Once.Adequacy.SourceFaithful.curry-transport
d_curry'45'transport_770 ::
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
d_curry'45'transport_770 = erased
-- Once.Adequacy.SourceFaithful.curry-body
d_curry'45'body_802 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'body_802 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_824 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_dγ''_824 v8
du_dγ''_824 :: AgdaAny -> AgdaAny
du_dγ''_824 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ef
d_ef_826 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ef_826 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10
  = du_ef_826 v2 v4 v5 v6 v7
du_ef_826 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_826 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
         (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_pure_34))
         (coe v3))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_832 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_832 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-curry-reduce
d_eval'7472''45'curry'45'reduce_848 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'curry'45'reduce_848 = erased
-- Once.Adequacy.SourceFaithful.fork-transport
d_fork'45'transport_916 ::
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
d_fork'45'transport_916 = erased
-- Once.Adequacy.SourceFaithful.fork-body
d_fork'45'body_960 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fork'45'body_960 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_986 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
           ~v13
  = du_dγ''_986 v10
du_dγ''_986 :: AgdaAny -> AgdaAny
du_dγ''_986 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ef
d_ef_988 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ef_988 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_ef_988 v2 v5 v6 v8
du_ef_988 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_988 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_pure_34))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.eg
d_eg_990 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eg_990 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
  = du_eg_990 v2 v5 v7 v9
du_eg_990 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_990 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_pure_34))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_996 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_996 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1010 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1010 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-fork-reduce
d_eval'7472''45'fork'45'reduce_1030 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'fork'45'reduce_1030 = erased
-- Once.Adequacy.SourceFaithful.copair-transport
d_copair'45'transport_1102 ::
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
d_copair'45'transport_1102 = erased
-- Once.Adequacy.SourceFaithful.copair-body
d_copair'45'body_1144 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_copair'45'body_1144 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1172 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14
  = du_dγ''_1172 v11
du_dγ''_1172 :: AgdaAny -> AgdaAny
du_dγ''_1172 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ef
d_ef_1174 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ef_1174 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13
          ~v14
  = du_ef_1174 v2 v5 v7 v8 v9
du_ef_1174 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_1174 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.eg
d_eg_1176 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eg_1176 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 ~v11 ~v12 ~v13
          ~v14
  = du_eg_1176 v2 v6 v7 v8 v10
du_eg_1176 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eg_1176 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1182 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1182 = erased
-- Once.Adequacy.SourceFaithful._.ihg-T
d_ihg'45'T_1196 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihg'45'T_1196 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-copair-reduce
d_eval'7472''45'copair'45'reduce_1212 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'copair'45'reduce_1212 = erased
-- Once.Adequacy.SourceFaithful._.branch
d_branch_1224 ::
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
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_branch_1224 = erased
-- Once.Adequacy.SourceFaithful.app-body
d_app'45'body_1282 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'body_1282 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1308 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny
d_dγ''_1308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13
  = du_dγ''_1308 v10
du_dγ''_1308 :: AgdaAny -> AgdaAny
du_dγ''_1308 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ef
d_ef_1310 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ef_1310 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_ef_1310 v2 v5 v6 v7 v8
du_ef_1310 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ef_1310 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1) (coe v3)
         (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4)
-- Once.Adequacy.SourceFaithful._.ex
d_ex_1312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ex_1312 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
  = du_ex_1312 v2 v5 v9
du_ex_1312 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ex_1312 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v2)
-- Once.Adequacy.SourceFaithful._.ihf-T
d_ihf'45'T_1318 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihf'45'T_1318 = erased
-- Once.Adequacy.SourceFaithful._.ihx-T
d_ihx'45'T_1328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ihx'45'T_1328 = erased
-- Once.Adequacy.SourceFaithful._.evalᴰ-app-reduce
d_eval'7472''45'app'45'reduce_1334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'app'45'reduce_1334 = erased
-- Once.Adequacy.SourceFaithful.faithful
d_faithful_1362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_faithful_1362 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1396 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_1396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_dγ''_1396 v10
du_dγ''_1396 :: AgdaAny -> AgdaAny
du_dγ''_1396 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee
d_ee_1398 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee_1398 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_ee_1398 v2 v5 v6 v9
du_ee_1398 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee_1398 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v1))
      (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.liftFn-curry-reduce
d_liftFn'45'curry'45'reduce_1402 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'curry'45'reduce_1402 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_1452 ::
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
d_dγ''_1452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_dγ''_1452 v9
du_dγ''_1452 :: AgdaAny -> AgdaAny
du_dγ''_1452 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.body
d_body_1454 ::
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
d_body_1454 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10
  = du_body_1454 v2 v5 v6 v7 v8
du_body_1454 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_body_1454 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe v0)))
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.C__'8667'__24
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)))
         (coe MAlonzo.Code.Once.IR.C_apply_92)
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v2))
               (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
               (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v4))
            (coe MAlonzo.Code.Once.IR.C_Heap_8)))
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Adequacy.SourceFaithful._.liftFn-curry-reduce-effApp
d_liftFn'45'curry'45'reduce'45'effApp_1458 ::
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
d_liftFn'45'curry'45'reduce'45'effApp_1458 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2032 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> AgdaAny
d_dγ''_2032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_dγ''_2032 v10
du_dγ''_2032 :: AgdaAny -> AgdaAny
du_dγ''_2032 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.ee1
d_ee1_2034 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee1_2034 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 ~v11
  = du_ee1_2034 v2 v7 v8
du_ee1_2034 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee1_2034 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v2)
-- Once.Adequacy.SourceFaithful._.ee2
d_ee2_2036 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> Integer -> MAlonzo.Code.Once.IR.T_IR_16
d_ee2_2036 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 v9 ~v10 ~v11
  = du_ee2_2036 v2 v3 v7 v9
du_ee2_2036 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ee2_2036 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
      (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.let-reduce
d_let'45'reduce_2040 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_let'45'reduce_2040 = erased
-- Once.Adequacy.SourceFaithful._.e2-eq
d_e2'45'eq_2046 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e2'45'eq_2046 = erased
-- Once.Adequacy.SourceFaithful._.dγ'
d_dγ''_2222 ::
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
d_dγ''_2222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15
  = du_dγ''_2222 v14
du_dγ''_2222 :: AgdaAny -> AgdaAny
du_dγ''_2222 v0 = coe v0
-- Once.Adequacy.SourceFaithful._.es
d_es_2224 ::
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
d_es_2224 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 ~v12 ~v13
          ~v14 ~v15
  = du_es_2224 v2 v9 v10 v11
du_es_2224 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_es_2224 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208 (coe v0)
      (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.ll
d_ll_2226 ::
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
d_ll_2226 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
          ~v14 ~v15
  = du_ll_2226 v2 v3 v9 v12
du_ll_2226 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ll_2226 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
      (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.rr
d_rr_2228 ::
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
d_rr_2228 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13
          ~v14 ~v15
  = du_rr_2228 v2 v3 v10 v13
du_rr_2228 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_rr_2228 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_208
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v2))
      (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v3)
-- Once.Adequacy.SourceFaithful._.reshape
d_reshape_2230 ::
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
d_reshape_2230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12 ~v13 v14 ~v15 v16
  = du_reshape_2230 v14 v16
du_reshape_2230 ::
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_reshape_2230 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v2)))
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v2)))
      v1
-- Once.Adequacy.SourceFaithful._.branchᴰ
d_branch'7472'_2238 ::
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
d_branch'7472'_2238 v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11
                    v12 v13 v14 ~v15
  = du_branch'7472'_2238 v0 v2 v3 v9 v10 v12 v13 v14
du_branch'7472'_2238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'7472'_2238 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v8 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
           (coe v0)
           (coe
              MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
              (coe
                 MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v3))))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
           (coe du_ll_2226 (coe v1) (coe v2) (coe v3) (coe v5))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v8)))
      (\ v8 ->
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
           (coe v0)
           (coe
              MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
              (coe
                 MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                 (coe
                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v4))))
           (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2))
           (coe du_rr_2228 (coe v1) (coe v2) (coe v4) (coe v6))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v8)))
-- Once.Adequacy.SourceFaithful._.dd-reduce
d_dd'45'reduce_2248 ::
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
d_dd'45'reduce_2248 = erased
-- Once.Adequacy.SourceFaithful._.case-fuse
d_case'45'fuse_2258 ::
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
d_case'45'fuse_2258 = erased
-- Once.Adequacy.SourceFaithful._.assoc-fuse
d_assoc'45'fuse_2268 ::
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
d_assoc'45'fuse_2268 = erased
-- Once.Adequacy.SourceFaithful._.case-reduce
d_case'45'reduce_2280 ::
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
d_case'45'reduce_2280 = erased
-- Once.Adequacy.SourceFaithful._.branch-eq
d_branch'45'eq_2290 ::
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
d_branch'45'eq_2290 = erased
