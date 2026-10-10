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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
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

-- Once.Adequacy.CataErased._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_12 ~v0 ~v1
  = du_coerce'45'base'45'to'45'full_12
du_coerce'45'base'45'to'45'full_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_12
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_786
-- Once.Adequacy.CataErased._.base-coh
d_base'45'coh_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'coh_16 = erased
-- Once.Adequacy.CataErased.subst-T-fmap
d_subst'45'T'45'fmap_28 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'fmap_28 = erased
-- Once.Adequacy.CataErased.subst-T-fmap-cancel
d_subst'45'T'45'fmap'45'cancel_48 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'fmap'45'cancel_48 = erased
-- Once.Adequacy.CataErased.subst-cong-μS
d_subst'45'cong'45'μS_64 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'cong'45'μS_64 = erased
-- Once.Adequacy.CataErased.cataS-subst-functor
d_cataS'45'subst'45'functor_84 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'subst'45'functor_84 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom
d_eval'7472''45'subst'45'dom_104 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom_104 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom-pair
d_eval'7472''45'subst'45'dom'45'pair_128 ::
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
d_eval'7472''45'subst'45'dom'45'pair_128 = erased
-- Once.Adequacy.CataErased.pairᴰ-subst⁻
d_pair'7472''45'subst'8315'_162 ::
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
d_pair'7472''45'subst'8315'_162 = erased
-- Once.Adequacy.CataErased.cata-ev-algᴰ-is-D
d_cata'45'ev'45'alg'7472''45'is'45'D_184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'ev'45'alg'7472''45'is'45'D_184 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₁
d_subst'45'S'8853''45'inj'8321'_214 ::
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
d_subst'45'S'8853''45'inj'8321'_214 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₂
d_subst'45'S'8853''45'inj'8322'_238 ::
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
d_subst'45'S'8853''45'inj'8322'_238 = erased
-- Once.Adequacy.CataErased.subst-S⊗
d_subst'45'S'8855'_266 ::
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
d_subst'45'S'8855'_266 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₁
d_push'7472''7477''45''43''8321'_286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8321'_286 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₂
d_push'7472''7477''45''43''8322'_304 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8322'_304 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-*
d_push'7472''7477''45''42'_324 ::
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
d_push'7472''7477''45''42'_324 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₁
d_push'7472''45''43''8321'_344 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8321'_344 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₂
d_push'7472''45''43''8322'_362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8322'_362 = erased
-- Once.Adequacy.CataErased.pushᴰ-*
d_push'7472''45''42'_382 ::
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
d_push'7472''45''42'_382 = erased
-- Once.Adequacy.CataErased.push-⊎₁
d_push'45''8846''8321'_406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'_406 = erased
-- Once.Adequacy.CataErased.push-⊎₂
d_push'45''8846''8322'_428 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'_428 = erased
-- Once.Adequacy.CataErased.push-×
d_push'45''215'_454 ::
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
d_push'45''215'_454 = erased
-- Once.Adequacy.CataErased.subst-SK
d_subst'45'SK_474 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK_474 = erased
-- Once.Adequacy.CataErased.base-z
d_base'45'z_488 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'z_488 = erased
-- Once.Adequacy.CataErased._.RelC
d_RelC_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelC_558 = erased
-- Once.Adequacy.CataErased._.LayerRel
d_LayerRel_568 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> ()
d_LayerRel_568 = erased
-- Once.Adequacy.CataErased._.RelT′-mono
d_RelT'8242''45'mono_596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelT'8242''45'mono_596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_RelT'8242''45'mono_596 v7 v8 v9 v10
du_RelT'8242''45'mono_596 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelT'8242''45'mono_596 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v7
               -> case coe v2 of
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v8
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
                           (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'call_690 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'call_690
                           (\ v15 ->
                              coe
                                du_RelT'8242''45'mono_596 (coe v0) (coe v11 v15) (coe v14 v15)
                                (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'halt_696
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'halt_696
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataErased._.id-step
d_id'45'step_616 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'45'step_616 = erased
-- Once.Adequacy.CataErased._.sum₁-step
d_sum'8321''45'step_636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'8321''45'step_636 = erased
-- Once.Adequacy.CataErased._.sum₂-step
d_sum'8322''45'step_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'8322''45'step_676 = erased
-- Once.Adequacy.CataErased._.prod-step
d_prod'45'step_720 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prod'45'step_720 = erased
-- Once.Adequacy.CataErased._.layer-rel
d_layer'45'rel_764 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_layer'45'rel_764 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_layer'45'rel_764 v3 v4 v5 v6 v7
du_layer'45'rel_764 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_layer'45'rel_764 v0 v1 v2 v3 v4
  = let v5
          = seq
              (coe v1)
              (coe
                 du_RelT'8242''45'mono_596 erased
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                       (coe
                          MAlonzo.Code.Once.IRTy.d_eraseF_50
                          (coe MAlonzo.Code.Once.Type.C_Id_114)))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                          (coe
                             MAlonzo.Code.Once.IRTy.d_eraseF_50
                             (coe MAlonzo.Code.Once.Type.C_Id_114)))
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_eraseF_50
                             (coe MAlonzo.Code.Once.Type.C_Id_114))
                          (coe
                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                             (coe MAlonzo.Code.Once.Type.C_Id_114)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242)))
                       (coe v2)))
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                    (coe MAlonzo.Code.Once.Type.C_Id_114)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                       (coe MAlonzo.Code.Once.Type.C_Id_114)
                       (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242) (coe v3)))
                 (coe v4)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_K_112 v6
           -> case coe v1 of
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v8
                  -> coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 erased
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
                  -> coe
                       du_RelT'8242''45'mono_596 erased
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                             (coe
                                MAlonzo.Code.Once.IRTy.d_eraseF_50
                                (coe MAlonzo.Code.Once.Type.C_Id_114)))
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114)))
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114))
                                (coe
                                   MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                   (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1)))
                             (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe MAlonzo.Code.Once.Type.C_Id_114)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1) (coe v3)))
                       (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C__'8853'__116 v6 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
                  -> coe
                       du_RelT'8242''45'mono_596 erased
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                             (coe
                                MAlonzo.Code.Once.IRTy.d_eraseF_50
                                (coe MAlonzo.Code.Once.Type.C_Id_114)))
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114)))
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114))
                                (coe
                                   MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                   (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1)))
                             (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe MAlonzo.Code.Once.Type.C_Id_114)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1) (coe v3)))
                       (coe v4)
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                -> coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_472
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                           (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                 (coe v6) (coe v10)))
                                           (coe v12)))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v6)
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                           (coe v6) (coe v10) (coe v13)))
                                     erased
                                     (coe
                                        du_layer'45'rel_764 (coe v6) (coe v10) (coe v12) (coe v13)
                                        (coe v4))
                              _ -> coe v5
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                -> coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_472
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                           (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7)))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                 (coe v7) (coe v11)))
                                           (coe v12)))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                           (coe v7) (coe v11) (coe v13)))
                                     erased
                                     (coe
                                        du_layer'45'rel_764 (coe v7) (coe v11) (coe v12) (coe v13)
                                        (coe v4))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C__'8855'__118 v6 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242
                  -> coe
                       du_RelT'8242''45'mono_596 erased
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                             (coe
                                MAlonzo.Code.Once.IRTy.d_eraseF_50
                                (coe MAlonzo.Code.Once.Type.C_Id_114)))
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114)))
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_eraseF_50
                                   (coe MAlonzo.Code.Once.Type.C_Id_114))
                                (coe
                                   MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                   (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1)))
                             (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                          (coe MAlonzo.Code.Once.Type.C_Id_114)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                             (coe MAlonzo.Code.Once.Type.C_Id_114) (coe v1) (coe v3)))
                       (coe v4)
                MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_422
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                                  (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                               (coe
                                                  MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                        (coe v6)))
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6))
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                        (coe v6) (coe v10)))
                                                  (coe v12)))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                               (coe v6)
                                               (coe
                                                  MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                                  (coe v6) (coe v10) (coe v14)))
                                            (coe
                                               du_layer'45'rel_764 (coe v6) (coe v10) (coe v12)
                                               (coe v14) (coe v16))
                                            (coe
                                               (\ v18 v19 v20 ->
                                                  coe
                                                    MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_422
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                                       (coe
                                                          MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                             (coe v7)))
                                                       (coe
                                                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                                             (coe
                                                                MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                                             (coe
                                                                MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                                (coe v7))
                                                             (coe
                                                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                                (coe v7) (coe v11)))
                                                          (coe v13)))
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                                       (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                                                          (coe v7) (coe v11) (coe v15)))
                                                    (coe
                                                       du_layer'45'rel_764 (coe v7) (coe v11)
                                                       (coe v13) (coe v15) (coe v17))
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          coe
                                                            MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
                                                            erased))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.Adequacy.CataErased._.evalᴰ-Cata-erased
d_eval'7472''45'Cata'45'erased_872 ::
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
d_eval'7472''45'Cata'45'erased_872 = erased
-- Once.Adequacy.CataErased._._.mir'
d_mir''_890 ::
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
d_mir''_890 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 = du_mir''_890 v6
du_mir''_890 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_mir''_890 v0 = coe v0
-- Once.Adequacy.CataErased._._.w'
d_w''_894 ::
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
d_w''_894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_w''_894 v8
du_w''_894 ::
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_w''_894 v0 = coe v0
-- Once.Adequacy.CataErased._._.seed-eq
d_seed'45'eq_898 ::
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
d_seed'45'eq_898 = erased
-- Once.Adequacy.CataErased._._.body
d_body_904 ::
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
d_body_904 = erased
-- Once.Adequacy.CataErased._._._.dalg_L
d_dalg_L_910 ::
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
d_dalg_L_910 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 v9
  = du_dalg_L_910 v0 v1 v2 v3 v4 v6 v7 v9
du_dalg_L_910 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_dalg_L_910 v0 v1 v2 v3 v4 v5 v6 v7
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
d_algL_916 ::
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
d_algL_916 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algL_916 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algL_916 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algL_916 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
         du_dalg_L_910 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
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
d_algL''_920 ::
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
d_algL''_920 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algL''_920 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algL''_920 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algL''_920 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_algL_916 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8)
-- Once.Adequacy.CataErased._._._.algM
d_algM_926 ::
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
d_algM_926 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_algM_926 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_algM_926 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_algM_926 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe v3) (coe v5)
      (coe
         (\ v9 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_392
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
d_Lr'8801'_934 ::
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
d_Lr'8801'_934 = erased
-- Once.Adequacy.CataErased._._._.from-subst-eq
d_from'45'subst'45'eq_940 ::
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
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_from'45'subst'45'eq_940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                          ~v10 ~v11
  = du_from'45'subst'45'eq_940 v9
du_from'45'subst'45'eq_940 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_from'45'subst'45'eq_940 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_'8801''45'RelT'8242'_558
      (coe v0)
-- Once.Adequacy.CataErased._._._.to-subst-eq
d_to'45'subst'45'eq_952 ::
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
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'45'subst'45'eq_952 = erased
-- Once.Adequacy.CataErased._._._.algR-full
d_algR'45'full_964 ::
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
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_algR'45'full_964 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_algR'45'full_964 v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
du_algR'45'full_964 ::
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
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_algR'45'full_964 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_422
      (coe du_mL_976 (coe v3) (coe v5) (coe v8))
      (coe du_mM_980 (coe v3) (coe v5) (coe v9))
      (coe
         du_layer'45'rel_764 (coe v3) (coe v5) (coe v8) (coe v9) (coe v10))
      (coe
         (\ v11 v12 v13 ->
            coe
              du_from'45'subst'45'eq_940
              (coe
                 du_contL_982 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                 (coe v6) (coe v7) (coe v11))))
-- Once.Adequacy.CataErased._._._._.mL
d_mL_976 ::
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
d_mL_976 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_mL_976 v3 v5 v9
du_mL_976 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_mL_976 v0 v1 v2
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
d_mM_980 ::
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
d_mM_980 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_mM_980 v3 v5 v10
du_mM_980 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_mM_980 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
         (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.CataErased._._._._.contL
d_contL_982 ::
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
d_contL_982 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contL_982 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_contL_982 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_contL_982 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_dalg_L_910 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
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
d_contM_986 ::
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
d_contM_986 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contM_986 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_contM_986 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_contM_986 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_392 (coe v0)
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
d_step'45'eq_994 ::
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
d_step'45'eq_994 = erased
-- Once.Adequacy.CataErased._._._.rc
d_rc_1022 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_rc_1022 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
         du_algR'45'full_964 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7))
      (coe v8)
-- Once.Adequacy.CataErased.liftFn-SigOp
d_liftFn'45'SigOp_1034 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'SigOp_1034 = erased
