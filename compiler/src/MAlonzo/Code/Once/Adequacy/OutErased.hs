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
import qualified MAlonzo.Code.Once.Adequacy.CataBridge
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.OutErased._.RelV
d_RelV_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelV_20 = erased
-- Once.Adequacy.OutErased.Out-ir
d_Out'45'ir_48 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_Out'45'ir_48 ~v0 v1 v2 = du_Out'45'ir_48 v1 v2
du_Out'45'ir_48 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Out'45'ir_48 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_118
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v1))
-- Once.Adequacy.OutErased.evalᴰ-subst-cod
d_eval'7472''45'subst'45'cod_72 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'cod_72 = erased
-- Once.Adequacy.OutErased.subst-TI-projTrace
d_subst'45'TI'45'projTrace_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'TI'45'projTrace_90 = erased
-- Once.Adequacy.OutErased.subst-TI-valueT
d_subst'45'TI'45'valueT_108 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'TI'45'valueT_108 = erased
-- Once.Adequacy.OutErased.subst-id-νᵈ
d_subst'45'id'45'ν'7496'_122 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'id'45'ν'7496'_122 = erased
-- Once.Adequacy.OutErased.forceᵈ-subst
d_force'7496''45'subst_136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_force'7496''45'subst_136 = erased
-- Once.Adequacy.OutErased.force-subst-trace
d_force'45'subst'45'trace_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_force'45'subst'45'trace_150 = erased
-- Once.Adequacy.OutErased.force-subst-value
d_force'45'subst'45'value_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_force'45'subst'45'value_168 = erased
-- Once.Adequacy.OutErased.out-trace
d_out'45'trace_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'trace_182 = erased
-- Once.Adequacy.OutErased.out-layerᴵ
d_out'45'layer'7477'_200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny
d_out'45'layer'7477'_200 ~v0 v1 v2 v3
  = du_out'45'layer'7477'_200 v1 v2 v3
du_out'45'layer'7477'_200 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny
du_out'45'layer'7477'_200 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1002
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         erased v2)
-- Once.Adequacy.OutErased.subst-diag-ν⁻
d_subst'45'diag'45'ν'8315'_224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'diag'45'ν'8315'_224 = erased
-- Once.Adequacy.OutErased.pushS⊕₁⁻
d_pushS'8853''8321''8315'_248 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8321''8315'_248 = erased
-- Once.Adequacy.OutErased.pushS⊕₂⁻
d_pushS'8853''8322''8315'_272 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8322''8315'_272 = erased
-- Once.Adequacy.OutErased.pushS⊗⁻
d_pushS'8855''8315'_300 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8855''8315'_300 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₁
d_push'45''43''7472''8321'_324 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8321'_324 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₂
d_push'45''43''7472''8322'_346 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8322'_346 = erased
-- Once.Adequacy.OutErased.push-*ᴰ
d_push'45''42''7472'_372 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''42''7472'_372 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₁⁻
d_push'45''43''7472''8321''8315'_396 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8321''8315'_396 = erased
-- Once.Adequacy.OutErased.push-+ᴰ₂⁻
d_push'45''43''7472''8322''8315'_418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7472''8322''8315'_418 = erased
-- Once.Adequacy.OutErased.push-*ᴰ⁻
d_push'45''42''7472''8315'_444 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''42''7472''8315'_444 = erased
-- Once.Adequacy.OutErased.push-+ᴵ₁⁻
d_push'45''43''7477''8321''8315'_464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7477''8321''8315'_464 = erased
-- Once.Adequacy.OutErased.push-+ᴵ₂⁻
d_push'45''43''7477''8322''8315'_482 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''43''7477''8322''8315'_482 = erased
-- Once.Adequacy.OutErased.push-*ᴵ⁻
d_push'45''42''7477''8315'_502 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''42''7477''8315'_502 = erased
-- Once.Adequacy.OutErased.out-layer-gen
d_out'45'layer'45'gen_516 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_out'45'layer'45'gen_516 ~v0 v1 v2 ~v3 v4
  = du_out'45'layer'45'gen_516 v1 v2 v4
du_out'45'layer'45'gen_516 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny
du_out'45'layer'45'gen_516 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1002
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         erased v2)
-- Once.Adequacy.OutErased.subst-SK-const
d_subst'45'SK'45'const_540 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK'45'const_540 = erased
-- Once.Adequacy.OutErased.pushSK⁻
d_pushSK'8315'_556 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushSK'8315'_556 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊕₁
d_out'45'layer'45'gen'45''8853''8321'_572 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8853''8321'_572 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊕₂
d_out'45'layer'45'gen'45''8853''8322'_598 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8853''8322'_598 = erased
-- Once.Adequacy.OutErased.out-layer-gen-⊗
d_out'45'layer'45'gen'45''8855'_626 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'layer'45'gen'45''8855'_626 = erased
-- Once.Adequacy.OutErased.base-out
d_base'45'out_650 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'out_650 = erased
-- Once.Adequacy.OutErased.νout-erase-D
d_νout'45'erase'45'D_728 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_νout'45'erase'45'D_728 = erased
-- Once.Adequacy.OutErased._.OUTK
d_OUTK_742 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> AgdaAny
d_OUTK_742 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_OUTK_742 v5
du_OUTK_742 :: AgdaAny -> AgdaAny
du_OUTK_742 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_OUT_772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_OUT_772 v7
du_OUT_772 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_OUT_772 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_802 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_OUT_802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_OUT_802 v7
du_OUT_802 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_OUT_802 v0 = coe v0
-- Once.Adequacy.OutErased._.OUT
d_OUT_834 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_OUT_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_OUT_834 v8
du_OUT_834 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_OUT_834 v0 = coe v0
-- Once.Adequacy.OutErased.out-coh
d_out'45'coh_856 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'coh_856 = erased
-- Once.Adequacy.OutErased.out-value
d_out'45'value_876 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'value_876 = erased
-- Once.Adequacy.OutErased.layer-refl
d_layer'45'refl_900 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_layer'45'refl_900 ~v0 ~v1 v2 v3 v4 v5
  = du_layer'45'refl_900 v2 v3 v4 v5
du_layer'45'refl_900 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_layer'45'refl_900 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v6
               -> coe
                    MAlonzo.Code.Once.Adequacy.CataBridge.du_base'45'refl_24 (coe v4)
                    (coe v6) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Id_112 -> coe seq (coe v1) (coe v2 v3)
      MAlonzo.Code.Once.Type.C__'8853'__114 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> coe du_layer'45'refl_900 (coe v4) (coe v8) (coe v2) (coe v10)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> coe du_layer'45'refl_900 (coe v5) (coe v9) (coe v2) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_layer'45'refl_900 (coe v4) (coe v8) (coe v2) (coe v10))
                           (coe du_layer'45'refl_900 (coe v5) (coe v9) (coe v2) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.OutErased.liftFn-Out-pair
d_liftFn'45'Out'45'pair_960 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftFn'45'Out'45'pair_960 ~v0 v1 v2 v3 v4
  = du_liftFn'45'Out'45'pair_960 v1 v2 v3 v4
du_liftFn'45'Out'45'pair_960 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_liftFn'45'Out'45'pair_960 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         du_layer'45'refl_900 (coe v0) (coe v1) erased
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
            (coe
               MAlonzo.Code.Once.Denotation.Meaning.d_out'45'sem_60 (coe v0)
               (coe v1) (coe v2))
            (coe v3)))
