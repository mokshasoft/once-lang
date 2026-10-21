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

module MAlonzo.Code.Once.Adequacy.OutErased where

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
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.OutErased.Out-ir
d_Out'45'ir_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_Out'45'ir_34 ~v0 ~v1 v2 ~v3 v4 = du_Out'45'ir_34 v2 v4
du_Out'45'ir_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Out'45'ir_34 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v1))
-- Once.Adequacy.OutErased.evalᴰ-subst-cod
d_eval'7472''45'subst'45'cod_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'cod_60 = erased
-- Once.Adequacy.OutErased.force-subst
d_force'45'subst_76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_force'45'subst_76 = erased
-- Once.Adequacy.OutErased.RelS-substF
d_RelS'45'substF_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'substF_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_RelS'45'substF_104 v11
du_RelS'45'substF_104 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'substF_104 v0 = coe v0
-- Once.Adequacy.OutErased.RelS-substF₀
d_RelS'45'substF'8320'_134 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'substF'8320'_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_RelS'45'substF'8320'_134 v11
du_RelS'45'substF'8320'_134 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'substF'8320'_134 v0 = coe v0
-- Once.Adequacy.OutErased.subst-diag-ν⁻
d_subst'45'diag'45'ν'8315'_154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'diag'45'ν'8315'_154 = erased
-- Once.Adequacy.OutErased.pushS⊕₁⁻
d_pushS'8853''8321''8315'_178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8321''8315'_178 = erased
-- Once.Adequacy.OutErased.pushS⊕₂⁻
d_pushS'8853''8322''8315'_202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8322''8315'_202 = erased
-- Once.Adequacy.OutErased.pushS⊗⁻
d_pushS'8855''8315'_230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8855''8315'_230 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₁⁻
d_push'45''43''7472''8321''8315'_254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8321''8315'_254 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₂⁻
d_push'45''43''7472''8322''8315'_276 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8322''8315'_276 = erased
-- Once.Adequacy.OutErased.push-*ᴰ⁻
d_push'45''42''7472''8315'_302 ::
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
d_push'45''42''7472''8315'_302 = erased
-- Once.Adequacy.OutErased.push-+ᴵ₁⁻
d_push'45''43''7477''8321''8315'_322 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7477''8321''8315'_322 = erased
-- Once.Adequacy.OutErased.push-+ᴵ₂⁻
d_push'45''43''7477''8322''8315'_340 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7477''8322''8315'_340 = erased
-- Once.Adequacy.OutErased.push-*ᴵ⁻
d_push'45''42''7477''8315'_360 ::
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
d_push'45''42''7477''8315'_360 = erased
-- Once.Adequacy.OutErased.out-layer-gen
d_out'45'layer'45'gen_374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_out'45'layer'45'gen_374 ~v0 ~v1 v2 v3 ~v4 v5
  = du_out'45'layer'45'gen_374 v2 v3 v5
du_out'45'layer'45'gen_374 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_out'45'layer'45'gen_374 v0 v1 v2
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
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         erased v2)
-- Once.Adequacy.OutErased.subst-SK-const
d_subst'45'SK'45'const_398 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK'45'const_398 = erased
-- Once.Adequacy.OutErased.pushSK⁻
d_pushSK'8315'_414 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushSK'8315'_414 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊕₁
d_out'45'layer'45'gen'45''8853''8321'_430 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8853''8321'_430 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊕₂
d_out'45'layer'45'gen'45''8853''8322'_456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8853''8322'_456 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊗
d_out'45'layer'45'gen'45''8855'_484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8855'_484 = erased
-- Once.Adequacy.OutErased.base-out
d_base'45'out_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'out_508 = erased
-- Once.Adequacy.OutErased.νout-erase-D
d_νout'45'erase'45'D_578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_νout'45'erase'45'D_578 = erased
-- Once.Adequacy.OutErased._.OUTK
d_OUTK_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_OUTK_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_OUTK_592 v6
du_OUTK_592 :: AgdaAny -> AgdaAny
du_OUTK_592 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_622 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_OUT_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_OUT_622 v8
du_OUT_622 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_OUT_622 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_652 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_OUT_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_OUT_652 v8
du_OUT_652 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_OUT_652 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_684 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_OUT_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_OUT_684 v9
du_OUT_684 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_OUT_684 v0 = coe v0
-- Once.Adequacy.OutErased.liftFn-Out
d_liftFn'45'Out_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_liftFn'45'Out_708 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7
  = du_liftFn'45'Out_708 v2 v4 v5 v6 v7
du_liftFn'45'Out_708 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_liftFn'45'Out_708 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
      (coe
         MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v2))
      (coe
         MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
      (coe du_g'8320'_732 (coe v0) (coe v1))
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584 v0 v1
                 erased v5)))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'mono_464
         (coe
            (\ v5 v6 v7 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v7))))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v2))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v4)))
      (coe
         (\ v5 v6 v7 ->
            case coe v7 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                -> case coe v9 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                       -> coe du_step_784 (coe v0) (coe v1) (coe v8) (coe v6) (coe v11)
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.OutErased._.X
d_X_726 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
d_X_726 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 = du_X_726 v2 v3
du_X_726 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_X_726 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v0)
      (coe
         MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v0) (coe v1))
-- Once.Adequacy.OutErased._.H
d_H_728 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6
d_H_728 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_H_728 v2
du_H_728 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6
du_H_728 v0
  = coe
      MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56 (coe v0)
-- Once.Adequacy.OutErased._.v₀
d_v'8320'_730 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14
d_v'8320'_730 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_v'8320'_730 v5
du_v'8320'_730 ::
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14
du_v'8320'_730 v0 = coe v0
-- Once.Adequacy.OutErased._.g₀
d_g'8320'_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  AgdaAny -> AgdaAny
d_g'8320'_732 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8
  = du_g'8320'_732 v2 v4 v8
du_g'8320'_732 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_g'8320'_732 v0 v1 v2
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
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         erased v2)
-- Once.Adequacy.OutErased._.g₁
d_g'8321'_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  AgdaAny -> AgdaAny
d_g'8321'_738 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8
  = du_g'8321'_738 v2 v4 v8
du_g'8321'_738 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_g'8321'_738 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584 v0 v1
         erased v2)
-- Once.Adequacy.OutErased._.R₀
d_R'8320'_742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  AgdaAny -> AgdaAny -> ()
d_R'8320'_742 = erased
-- Once.Adequacy.OutErased._.≡ˢ
d_'8801''738'_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''738'_764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 v15
  = du_'8801''738'_764 v15
du_'8801''738'_764 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''738'_764 v0 = coe v0
-- Once.Adequacy.OutErased._.≡ᴰ
d_'8801''7472'_774 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8801''7472'_774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12
  = du_'8801''7472'_774 v12
du_'8801''7472'_774 :: AgdaAny -> AgdaAny
du_'8801''7472'_774 v0 = coe v0
-- Once.Adequacy.OutErased._.step
d_step_784 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_step_784 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_step_784 v2 v4 v8 v9 v10
du_step_784 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_step_784 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v0)
         (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_cμout'45'rel_1284 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.du_layer'8594'srel_1530
            (coe du_H_728 (coe v0)) (coe v2) (coe v3) (coe v4)))
