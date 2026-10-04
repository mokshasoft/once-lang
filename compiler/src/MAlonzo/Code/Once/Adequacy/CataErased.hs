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

module MAlonzo.Code.Once.Adequacy.CataErased where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataErased.subst-T-fmap
d_subst'45'T'45'fmap_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'fmap_20 = erased
-- Once.Adequacy.CataErased.subst-T-fmap-cancel
d_subst'45'T'45'fmap'45'cancel_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'fmap'45'cancel_40 = erased
-- Once.Adequacy.CataErased.subst-cong-μS
d_subst'45'cong'45'μS_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'cong'45'μS_56 = erased
-- Once.Adequacy.CataErased.cataS-subst-functor
d_cataS'45'subst'45'functor_76 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'subst'45'functor_76 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom
d_eval'7472''45'subst'45'dom_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom_96 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom-pair
d_eval'7472''45'subst'45'dom'45'pair_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom'45'pair_120 = erased
-- Once.Adequacy.CataErased.pairᴰ-subst⁻
d_pair'7472''45'subst'8315'_154 ::
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
d_pair'7472''45'subst'8315'_154 = erased
-- Once.Adequacy.CataErased.cata-ev-algᴰ-is-D
d_cata'45'ev'45'alg'7472''45'is'45'D_176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'ev'45'alg'7472''45'is'45'D_176 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₁
d_subst'45'S'8853''45'inj'8321'_206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8321'_206 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₂
d_subst'45'S'8853''45'inj'8322'_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8322'_230 = erased
-- Once.Adequacy.CataErased.subst-S⊗
d_subst'45'S'8855'_258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8855'_258 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₁
d_push'7472''7477''45''43''8321'_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8321'_278 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₂
d_push'7472''7477''45''43''8322'_296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8322'_296 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-*
d_push'7472''7477''45''42'_316 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''42'_316 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₁
d_push'7472''45''43''8321'_336 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8321'_336 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₂
d_push'7472''45''43''8322'_354 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8322'_354 = erased
-- Once.Adequacy.CataErased.pushᴰ-*
d_push'7472''45''42'_374 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''42'_374 = erased
-- Once.Adequacy.CataErased.push-⊎₁
d_push'45''8846''8321'_398 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'_398 = erased
-- Once.Adequacy.CataErased.push-⊎₂
d_push'45''8846''8322'_420 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'_420 = erased
-- Once.Adequacy.CataErased.push-×
d_push'45''215'_446 ::
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
d_push'45''215'_446 = erased
-- Once.Adequacy.CataErased.subst-SK
d_subst'45'SK_466 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK_466 = erased
-- Once.Adequacy.CataErased._.RelC
d_RelC_476 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelC_476 = erased
-- Once.Adequacy.CataErased._.LayerRel
d_LayerRel_486 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> ()
d_LayerRel_486 = erased
-- Once.Adequacy.CataErased._.layer-rel
d_layer'45'rel_508
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CataErased._.layer-rel"
-- Once.Adequacy.CataErased._.evalᴰ-Cata-erased
d_eval'7472''45'Cata'45'erased_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'Cata'45'erased_526 = erased
-- Once.Adequacy.CataErased._._.mir'
d_mir''_544 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_mir''_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 = du_mir''_544 v6
du_mir''_544 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_mir''_544 v0 = coe v0
-- Once.Adequacy.CataErased._._.w'
d_w''_548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_w''_548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_w''_548 v8
du_w''_548 ::
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_w''_548 v0 = coe v0
-- Once.Adequacy.CataErased._._.seed-eq
d_seed'45'eq_552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'eq_552 = erased
-- Once.Adequacy.CataErased._._.body
d_body_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_558 = erased
-- Once.Adequacy.CataErased._._._.dalg_L
d_dalg_L_564 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_dalg_L_564 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9
  = du_dalg_L_564 v0 v1 v2 v3 v4 v6 v7 v9
du_dalg_L_564 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_dalg_L_564 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v5)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
-- Once.Adequacy.CataErased._._._.algL
d_algL_570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_algL_570 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algL_570 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algL_570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algL_570 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
      (coe
         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
            (coe v5)))
      (coe
         du_dalg_L_564 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
         (coe v7))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
               (coe v5)))
         (coe v8))
-- Once.Adequacy.CataErased._._._.algL'
d_algL''_574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_algL''_574 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algL''_574 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algL''_574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algL''_574 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_algL_570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8)
-- Once.Adequacy.CataErased._._._.algM
d_algM_580 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_algM_580 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algM_580 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algM_580 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algM_580 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe v3) (coe v5)
      (coe
         (\ v9 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_390
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'42'__124 (coe v4)
                 (coe
                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v3) (coe v2)))
              (coe v2) (coe v6)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v9))))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
         (coe v3) (coe v5) (coe v8))
-- Once.Adequacy.CataErased._._._.Lr≡
d_Lr'8801'_588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Lr'8801'_588 = erased
-- Once.Adequacy.CataErased._._._.from-subst-eq
d_from'45'subst'45'eq_594 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_from'45'subst'45'eq_594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                          ~v10 ~v11
  = du_from'45'subst'45'eq_594 v9
du_from'45'subst'45'eq_594 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
du_from'45'subst'45'eq_594 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_'8801''45'RelT'8242'_1268
      (coe v0)
-- Once.Adequacy.CataErased._._._.to-subst-eq
d_to'45'subst'45'eq_606 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'45'subst'45'eq_606 = erased
-- Once.Adequacy.CataErased._._._.algR-full
d_algR'45'full_618 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_algR'45'full_618 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_algR'45'full_618 v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
du_algR'45'full_618 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
du_algR'45'full_618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_1132
      (coe du_mL_630 (coe v3) (coe v5) (coe v8))
      (coe du_mM_634 (coe v3) (coe v5) (coe v9))
      (coe d_layer'45'rel_508 v0 v1 v2 v3 v5 v8 v9 v10)
      (coe
         (\ v11 v12 v13 ->
            coe
              du_from'45'subst'45'eq_594
              (coe
                 du_contL_636 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                 (coe v6) (coe v7) (coe v11))))
-- Once.Adequacy.CataErased._._._._.mL
d_mL_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_mL_630 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_mL_630 v3 v5 v9
du_mL_630 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_mL_630 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
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
-- Once.Adequacy.CataErased._._._._.mM
d_mM_634 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_mM_634 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_mM_634 v3 v5 v10
du_mM_634 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_mM_634 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
         (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.CataErased._._._._.contL
d_contL_636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_contL_636 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contL_636 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_contL_636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_contL_636 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_dalg_L_564 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
      (coe v7)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
               (coe v5)))
         (coe v8))
-- Once.Adequacy.CataErased._._._._.contM
d_contM_640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_contM_640 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contM_640 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_contM_640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_contM_640 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_390 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.Type.C__'42'__124 (coe v4)
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v3) (coe v2)))
      (coe v2) (coe v6)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
            (coe v3) (coe v5) (coe v8)))
-- Once.Adequacy.CataErased._._._._.step-eq
d_step'45'eq_648 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_648 = erased
-- Once.Adequacy.CataErased._._._.rc
d_rc_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_rc_676 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v3))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                    (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                          (coe v5)))
                    (coe v9)))
              (coe
                 (\ v10 ->
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                      (coe v0) (coe v1)
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                            (coe
                               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                               (coe
                                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                                  (coe v5)))
                            (coe v10)))))))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe v3) (coe v5) (coe v9)))
              (coe
                 (\ v10 ->
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                      (coe v0) (coe v1)
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v3) (coe v2))))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                            (coe v3) (coe v5) (coe v10)))))))
      (coe
         du_algR'45'full_618 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7))
      (coe v8)
-- Once.Adequacy.CataErased.liftFn-SigOp
d_liftFn'45'SigOp_688 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'SigOp_688 = erased
