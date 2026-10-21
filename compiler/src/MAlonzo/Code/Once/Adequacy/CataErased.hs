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
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.CataErased._.coerce-base-to-full
d_coerce'45'base'45'to'45'full_12 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_12 ~v0 ~v1
  = du_coerce'45'base'45'to'45'full_12
du_coerce'45'base'45'to'45'full_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_12
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Adequacy.CataErased._.base-coh
d_base'45'coh_16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'coh_16 = erased
-- Once.Adequacy.CataErased.subst-cong-μS
d_subst'45'cong'45'μS_28 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'cong'45'μS_28 = erased
-- Once.Adequacy.CataErased.cataS-subst-functor
d_cataS'45'subst'45'functor_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'subst'45'functor_48 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom
d_eval'7472''45'subst'45'dom_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom_68 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom-pair
d_eval'7472''45'subst'45'dom'45'pair_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom'45'pair_92 = erased
-- Once.Adequacy.CataErased.pairᴰ-subst⁻
d_pair'7472''45'subst'8315'_126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'7472''45'subst'8315'_126 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₁
d_subst'45'S'8853''45'inj'8321'_152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8321'_152 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₂
d_subst'45'S'8853''45'inj'8322'_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8322'_176 = erased
-- Once.Adequacy.CataErased.subst-S⊗
d_subst'45'S'8855'_204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8855'_204 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₁
d_push'7472''7477''45''43''8321'_224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8321'_224 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₂
d_push'7472''7477''45''43''8322'_242 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8322'_242 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-*
d_push'7472''7477''45''42'_262 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''42'_262 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₁
d_push'7472''45''43''8321'_282 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8321'_282 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₂
d_push'7472''45''43''8322'_300 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8322'_300 = erased
-- Once.Adequacy.CataErased.pushᴰ-*
d_push'7472''45''42'_320 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''42'_320 = erased
-- Once.Adequacy.CataErased.push-⊎₁
d_push'45''8846''8321'_344 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'_344 = erased
-- Once.Adequacy.CataErased.push-⊎₂
d_push'45''8846''8322'_366 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'_366 = erased
-- Once.Adequacy.CataErased.push-×
d_push'45''215'_392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'_392 = erased
-- Once.Adequacy.CataErased.subst-SK
d_subst'45'SK_412 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK_412 = erased
-- Once.Adequacy.CataErased.base-z
d_base'45'z_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'z_426 = erased
-- Once.Adequacy.CataErased.push-⊎₁⁺
d_push'45''8846''8321''8314'_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321''8314'_508 = erased
-- Once.Adequacy.CataErased.push-⊎₂⁺
d_push'45''8846''8322''8314'_530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322''8314'_530 = erased
-- Once.Adequacy.CataErased.push-×⁺
d_push'45''215''8314'_556 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215''8314'_556 = erased
-- Once.Adequacy.CataErased.RelS-substˡ⁻
d_RelS'45'subst'737''8315'_582 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'subst'737''8315'_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_RelS'45'subst'737''8315'_582 v9
du_RelS'45'subst'737''8315'_582 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'subst'737''8315'_582 v0 = coe v0
-- Once.Adequacy.CataErased._.RelC
d_RelC_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()
d_RelC_592 = erased
-- Once.Adequacy.CataErased._.L
d_L_602 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_L_602 ~v0 ~v1 ~v2 v3 v4 v5 = du_L_602 v3 v4 v5
du_L_602 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_L_602 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
      (coe
         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
            (coe v1)))
      (coe v2)
-- Once.Adequacy.CataErased._.LayerRel
d_LayerRel_612 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> ()
d_LayerRel_612 = erased
-- Once.Adequacy.CataErased._.≡ˡᴰ
d_'8801''737''7472'_632 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8801''737''7472'_632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8801''737''7472'_632 v8
du_'8801''737''7472'_632 :: AgdaAny -> AgdaAny
du_'8801''737''7472'_632 v0 = coe v0
-- Once.Adequacy.CataErased._.sum₁-step
d_sum'8321''45'step_650 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sum'8321''45'step_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_sum'8321''45'step_650 v9
du_sum'8321''45'step_650 :: AgdaAny -> AgdaAny
du_sum'8321''45'step_650 v0 = coe v0
-- Once.Adequacy.CataErased._.sum₂-step
d_sum'8322''45'step_680 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sum'8322''45'step_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_sum'8322''45'step_680 v9
du_sum'8322''45'step_680 :: AgdaAny -> AgdaAny
du_sum'8322''45'step_680 v0 = coe v0
-- Once.Adequacy.CataErased._.prod-step
d_prod'45'step_714 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prod'45'step_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   v12
  = du_prod'45'step_714 v11 v12
du_prod'45'step_714 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prod'45'step_714 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Adequacy.CataErased._.base-step
d_base'45'step_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_base'45'step_748 ~v0 ~v1 ~v2 v3 v4 v5
  = du_base'45'step_748 v3 v4 v5
du_base'45'step_748 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_base'45'step_748 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.d_base'45'refl_420 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
         (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
            (coe v0) (coe v1) (coe v2)))
-- Once.Adequacy.CataErased._.layer-rel
d_layer'45'rel_770 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_layer'45'rel_770 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_layer'45'rel_770 v3 v4 v5 v6 v7
du_layer'45'rel_770 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_layer'45'rel_770 v0 v1 v2 v3 v4
  = let v5 = seq (coe v1) (coe v4) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C_K_12 v6
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v8
                  -> coe
                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                       (coe du_base'45'step_748 (coe v6) (coe v8) (coe v2))
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v6 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                -> coe
                                     MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                           (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                 (coe v6) (coe v10)))
                                           (coe v12)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                           (coe v6) (coe v10) (coe v13)))
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                                     (coe
                                        du_layer'45'rel_770 (coe v6) (coe v10) (coe v12) (coe v13)
                                        (coe v4))
                                     (coe (\ v14 v15 v16 -> v16))
                              _ -> coe v5
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                         -> case coe v3 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                -> coe
                                     MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                           (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7)))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                              (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v7))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                 (coe v7) (coe v11)))
                                           (coe v12)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                           (coe v7) (coe v11) (coe v13)))
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                                     (coe
                                        du_layer'45'rel_770 (coe v7) (coe v11) (coe v12) (coe v13)
                                        (coe v4))
                                     (coe (\ v14 v15 v16 -> v16))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v6 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
                MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                            (coe
                                               MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                  (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v6)))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
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
                                               MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                               (coe v6)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                  (coe v6) (coe v10) (coe v14)))
                                            (coe
                                               (\ v18 ->
                                                  coe
                                                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                       (coe
                                                          MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                             (coe v7)))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
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
                                                       (\ v19 ->
                                                          coe
                                                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v18) (coe v19))))))
                                            (coe
                                               (\ v18 ->
                                                  coe
                                                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                       (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                          (coe v7) (coe v11) (coe v15)))
                                                    (coe
                                                       (\ v19 ->
                                                          coe
                                                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v18) (coe v19))))))
                                            (coe
                                               du_layer'45'rel_770 (coe v6) (coe v10) (coe v12)
                                               (coe v14) (coe v16))
                                            (coe
                                               (\ v18 v19 v20 ->
                                                  coe
                                                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                       (coe
                                                          MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_eraseF_50
                                                             (coe v7)))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                          (coe
                                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
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
                                                       MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                       (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                                                          (coe v7) (coe v11) (coe v15)))
                                                    (coe
                                                       (\ v21 ->
                                                          coe
                                                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v18) (coe v21))))
                                                    (coe
                                                       (\ v21 ->
                                                          coe
                                                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v19) (coe v21))))
                                                    (coe
                                                       du_layer'45'rel_770 (coe v7) (coe v11)
                                                       (coe v13) (coe v15) (coe v17))
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          coe
                                                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                            (coe
                                                               du_prod'45'step_714 (coe v20)
                                                               (coe v23))))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.Adequacy.CataErased._.cata-erased-rel
d_cata'45'erased'45'rel_892 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'erased'45'rel_892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_cataS'45'rel_1360
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
         (coe v3))
      (coe
         (\ v11 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                    (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                 (coe
                    MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                          (coe v5)))
                    (coe v11)))
              (coe
                 (\ v12 ->
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
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                            (coe
                               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                               (coe
                                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                                  (coe v5)))
                            (coe v12)))))))
      (coe
         (\ v11 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v3)
                    (coe v5) (coe v11)))
              (coe
                 (\ v12 ->
                    coe
                      v8
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                         (coe v3) (coe v5) (coe v12))))))
      (coe
         du_algR_980 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9))
      (coe v10)
-- Once.Adequacy.CataErased._._.≡ˢ
d_'8801''738'_926 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''738'_926 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18
  = du_'8801''738'_926 v18
du_'8801''738'_926 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''738'_926 v0 = coe v0
-- Once.Adequacy.CataErased._._.mir'
d_mir''_930 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_mir''_930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_mir''_930 v6
du_mir''_930 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_mir''_930 v0 = coe v0
-- Once.Adequacy.CataErased._._.env₀
d_env'8320'_934 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_env'8320'_934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_env'8320'_934 v7
du_env'8320'_934 :: AgdaAny -> AgdaAny
du_env'8320'_934 v0 = coe v0
-- Once.Adequacy.CataErased._._.w'
d_w''_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_w''_938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_w''_938 v10
du_w''_938 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
du_w''_938 v0 = coe v0
-- Once.Adequacy.CataErased._._.seed-eq
d_seed'45'eq_942 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'eq_942 = erased
-- Once.Adequacy.CataErased._._.algL
d_algL_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_algL_946 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_algL_946 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_algL_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_algL_946 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_cata'45'ev'45'alg'7472'_130
      (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (coe
         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
         (coe v5))
      (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
               (coe v5)))
         (coe v8))
-- Once.Adequacy.CataErased._._.algL'
d_algL''_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_algL''_950 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_algL''_950 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_algL''_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_algL''_950 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_algL_946 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8)
-- Once.Adequacy.CataErased._._.Lr≡
d_Lr'8801'_956 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Lr'8801'_956 = erased
-- Once.Adequacy.CataErased._._.step
d_step_962 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_step_962 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12 v13
  = du_step_962 v3 v5 v9 v11 v12 v13
du_step_962 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_step_962 v0 v1 v2 v3 v4 v5
  = coe
      v2
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         (coe v3))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
         (coe v0) (coe v1) (coe v4))
      v5
-- Once.Adequacy.CataErased._._.algR
d_algR_980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_algR_980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12 v13
  = du_algR_980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_algR_980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_algR_980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
         (coe
            MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478
            (coe
               MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
               (coe
                  MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                  (coe v5)))
            (coe v10)))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v3)
         (coe
            MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v3)
            (coe v5) (coe v11)))
      (coe
         (\ v13 ->
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
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3)))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                       (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v3))
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v3)
                          (coe v5)))
                    (coe v13)))))
      (coe
         (\ v13 ->
            coe
              v8
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                 (coe v3) (coe v5) (coe v13))))
      (coe
         du_layer'45'rel_770 (coe v3) (coe v5) (coe v10) (coe v11)
         (coe v12))
      (coe
         (\ v13 v14 ->
            coe du_step_962 (coe v3) (coe v5) (coe v9) (coe v13) (coe v14)))
-- Once.Adequacy.CataErased.liftFn-SigOp
d_liftFn'45'SigOp_1000 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'SigOp_1000 = erased
-- Once.Adequacy.CataErased._.cancel
d_cancel_1028 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cancel_1028 = erased
