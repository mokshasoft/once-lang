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

module MAlonzo.Code.Once.Adequacy.FaithfulLemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.FaithfulLemmas.σ₀
d_σ'8320'_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70
d_σ'8320'_32 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
      (coe v0) (coe v1)
-- Once.Adequacy.FaithfulLemmas.transport-apply-bind
d_transport'45'apply'45'bind_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transport'45'apply'45'bind_60 = erased
-- Once.Adequacy.FaithfulLemmas.subst-T-returnT
d_subst'45'T'45'returnT_76 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_76 = erased
-- Once.Adequacy.FaithfulLemmas.subst-arrow
d_subst'45'arrow_104 ::
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
d_subst'45'arrow_104 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge
d_morph'45'app'45'bridge_122 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge_122 = erased
-- Once.Adequacy.FaithfulLemmas._.w'
d_w''_140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_w''_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_w''_140 v7
du_w''_140 :: AgdaAny -> AgdaAny
du_w''_140 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.app-⟨⟩-clean
d_app'45''10216''10217''45'clean_146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45''10216''10217''45'clean_146 = erased
-- Once.Adequacy.FaithfulLemmas._.ih-evalᴰ
d_ih'45'eval'7472'_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ih'45'eval'7472'_154 = erased
-- Once.Adequacy.FaithfulLemmas.morph-app-bridge-fun
d_morph'45'app'45'bridge'45'fun_170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_morph'45'app'45'bridge'45'fun_170 = erased
-- Once.Adequacy.FaithfulLemmas.cataM-fold
d_cataM'45'fold_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataM'45'fold_182 = erased
-- Once.Adequacy.FaithfulLemmas._.c'
d_c''_198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_c''_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_c''_198 v6
du_c''_198 ::
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_c''_198 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.applyIR
d_applyIR_202 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_applyIR_202 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 = du_applyIR_202 v2 v3
du_applyIR_202 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> MAlonzo.Code.Once.IR.T_IR_16
du_applyIR_202 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1))))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe MAlonzo.Code.Once.IR.C_fst_42)
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.FaithfulLemmas._.apply-closure
d_apply'45'closure_206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'closure_206 = erased
-- Once.Adequacy.FaithfulLemmas._.innerCata
d_innerCata_212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_innerCata_212 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_innerCata_212 v2 v3 v5
du_innerCata_212 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_innerCata_212 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_Cata_106
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v2))
      (coe du_applyIR_202 (coe v0) (coe v1))
-- Once.Adequacy.FaithfulLemmas.cata-body
d_cata'45'body_250 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'body_250 = erased
-- Once.Adequacy.FaithfulLemmas._.ealg
d_ealg_274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ealg_274 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 ~v11
  = du_ealg_274 v2 v3 v4 v5 v6 v7 v9
du_ealg_274 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ealg_274 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v3) (coe v4))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
         (coe v4))
      (coe v6)
-- Once.Adequacy.FaithfulLemmas._.cataM'
d_cataM''_276 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_cataM''_276 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_cataM''_276 v5 v6 v8
du_cataM''_276 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_cataM''_276 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_cataM_364 (coe v0) (coe v1)
      (coe v2)
-- Once.Adequacy.FaithfulLemmas._.liftCataM
d_liftCataM_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_liftCataM_278 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
  = du_liftCataM_278 v0 v1 v5 v6 v7 v8
du_liftCataM_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_liftCataM_278 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_390 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
         (coe v3))
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v2))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
         (coe v3))
      (coe du_cataM''_276 (coe v2) (coe v3) (coe v5))
-- Once.Adequacy.FaithfulLemmas._.split
d_split_280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split_280 = erased
-- Once.Adequacy.FaithfulLemmas._.fold-step
d_fold'45'step_286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'step_286 = erased
-- Once.Adequacy.FaithfulLemmas.evalᴰ-subst-cod
d_eval'7472''45'subst'45'cod_306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'cod_306 = erased
-- Once.Adequacy.FaithfulLemmas.subst-fam-fmap
d_subst'45'fam'45'fmap_332 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'fam'45'fmap_332 = erased
-- Once.Adequacy.FaithfulLemmas.subst-id-cong
d_subst'45'id'45'cong_354 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'id'45'cong_354 = erased
-- Once.Adequacy.FaithfulLemmas.coerce-ν-in-subst
d_coerce'45'ν'45'in'45'subst_374 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'subst_374 = erased
-- Once.Adequacy.FaithfulLemmas.subst-fam-T
d_subst'45'fam'45'T_394 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'fam'45'T_394 = erased
-- Once.Adequacy.FaithfulLemmas.ana-body
d_ana'45'body_420 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'body_420 = erased
-- Once.Adequacy.FaithfulLemmas._.coalgIR
d_coalgIR_444 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_coalgIR_444 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11
  = du_coalgIR_444 v4 v5 v7 v9
du_coalgIR_444 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_coalgIR_444 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                        (coe (0 :: Integer))))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
               (coe
                  MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v0) (coe v1)))
               (coe v3))
            (coe MAlonzo.Code.Once.IR.C_terminal_72))
         (coe MAlonzo.Code.Once.IR.C_id_20))
-- Once.Adequacy.FaithfulLemmas._.coalg'
d_coalg''_446 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_coalg''_446 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11
  = du_coalg''_446 v4 v5 v7 v9
du_coalg''_446 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_coalg''_446 v0 v1 v2 v3
  = coe du_coalgIR_444 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.FaithfulLemmas._.Ana-IR
d_Ana'45'IR_450 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16
d_Ana'45'IR_450 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11
  = du_Ana'45'IR_450 v4 v5 v7 v8 v9
du_Ana'45'IR_450 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Ana'45'IR_450 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C_Ana_120
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v3))
      (coe du_coalg''_446 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Adequacy.FaithfulLemmas._.elab-ana-reduce
d_elab'45'ana'45'reduce_454 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'ana'45'reduce_454 = erased
-- Once.Adequacy.FaithfulLemmas._.cE
d_cE_464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_cE_464 v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
  = du_cE_464 v0 v1 v4 v5 v7 v8 v9 v12
du_cE_464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_cE_464 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
              (coe
                 MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                 (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2)))
              (coe
                 MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                 (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2))
                 (coe
                    MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v2)
                    (coe v5)))
              (coe v8)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe v1) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
         (coe du_coalg''_446 (coe v2) (coe v3) (coe v4) (coe v6)) (coe v7))
-- Once.Adequacy.FaithfulLemmas._.cS
d_cS_472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_cS_472 v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 ~v10 ~v11 v12
  = du_cS_472 v0 v1 v4 v5 v7 v8 v9 v12
du_cS_472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_cS_472 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
         (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2) (coe v3)))
            (coe v6) (coe v0) (coe d_σ'8320'_32 (coe v0) (coe v1))
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe (\ v8 -> coe v8 v7)))
-- Once.Adequacy.FaithfulLemmas._.coalg-agree
d_coalg'45'agree_490 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coalg'45'agree_490 = erased
-- Once.Adequacy.FaithfulLemmas._.push-subst-fn
d_push'45'subst'45'fn_506 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45'subst'45'fn_506 = erased
-- Once.Adequacy.FaithfulLemmas._.seedOf
d_seedOf_510 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_seedOf_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_seedOf_510 v12
du_seedOf_510 :: AgdaAny -> AgdaAny
du_seedOf_510 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.e-eq
d_e'45'eq_518 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e'45'eq_518 = erased
-- Once.Adequacy.FaithfulLemmas._.s-eq
d_s'45'eq_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'45'eq_526 = erased
-- Once.Adequacy.FaithfulLemmas._.per-x-D179
d_per'45'x'45'D179_536 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_per'45'x'45'D179_536 = erased
-- Once.Adequacy.FaithfulLemmas._._.M
d_M_544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_M_544 v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11 v12
  = du_M_544 v0 v1 v4 v5 v7 v9 v12
du_M_544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_M_544 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe v1) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2) (coe v3)))
      (coe du_coalgIR_444 (coe v2) (coe v3) (coe v4) (coe v5)) (coe v6)
-- Once.Adequacy.FaithfulLemmas._._.fM
d_fM_546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_fM_546 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_fM_546 v4 v8 v13
du_fM_546 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_fM_546 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
      (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
      erased
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         (coe v2))
-- Once.Adequacy.FaithfulLemmas._._.fI
d_fI_550 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_fI_550 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_fI_550 v4 v8 v13
du_fI_550 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_fI_550 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120
      (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
      erased
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         (coe v2))
-- Once.Adequacy.FaithfulLemmas._._.inner
d_inner_556 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_556 = erased
-- Once.Adequacy.FaithfulLemmas._._.lhs
d_lhs_574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs_574 = erased
-- Once.Adequacy.FaithfulLemmas._._.rhs
d_rhs_594 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rhs_594 = erased
-- Once.Adequacy.FaithfulLemmas._.ana-agree
d_ana'45'agree_610 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'agree_610 = erased
-- Once.Adequacy.FaithfulLemmas._.per-a
d_per'45'a_626 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_per'45'a_626 = erased
