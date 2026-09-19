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
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
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

-- Once.Adequacy.CataErased.subst-T-apply
d_subst'45'T'45'apply_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'apply_20 = erased
-- Once.Adequacy.CataErased.subst-T-projTrace
d_subst'45'T'45'projTrace_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'projTrace_36 = erased
-- Once.Adequacy.CataErased.subst-T-valueT
d_subst'45'T'45'valueT_54 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'valueT_54 = erased
-- Once.Adequacy.CataErased.subst-cong-μS
d_subst'45'cong'45'μS_70 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'cong'45'μS_70 = erased
-- Once.Adequacy.CataErased.cataS-subst-functor
d_cataS'45'subst'45'functor_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'subst'45'functor_90 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom
d_eval'7472''45'subst'45'dom_110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom_110 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom-pair
d_eval'7472''45'subst'45'dom'45'pair_134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom'45'pair_134 = erased
-- Once.Adequacy.CataErased.pairᴰ-subst⁻
d_pair'7472''45'subst'8315'_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'7472''45'subst'8315'_168 = erased
-- Once.Adequacy.CataErased.cata-ev-algᴰ-is-D
d_cata'45'ev'45'alg'7472''45'is'45'D_188 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'ev'45'alg'7472''45'is'45'D_188 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₁
d_subst'45'S'8853''45'inj'8321'_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8321'_216 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₂
d_subst'45'S'8853''45'inj'8322'_240 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8322'_240 = erased
-- Once.Adequacy.CataErased.subst-S⊗
d_subst'45'S'8855'_268 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8855'_268 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₁
d_push'7472''7477''45''43''8321'_288 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8321'_288 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₂
d_push'7472''7477''45''43''8322'_306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8322'_306 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-*
d_push'7472''7477''45''42'_326 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''42'_326 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₁
d_push'7472''45''43''8321'_346 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8321'_346 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₂
d_push'7472''45''43''8322'_364 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8322'_364 = erased
-- Once.Adequacy.CataErased.pushᴰ-*
d_push'7472''45''42'_384 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''42'_384 = erased
-- Once.Adequacy.CataErased.push-⊎₁
d_push'45''8846''8321'_408 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'_408 = erased
-- Once.Adequacy.CataErased.push-⊎₂
d_push'45''8846''8322'_430 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'_430 = erased
-- Once.Adequacy.CataErased.push-×
d_push'45''215'_456 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'_456 = erased
-- Once.Adequacy.CataErased.subst-SK
d_subst'45'SK_476 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK_476 = erased
-- Once.Adequacy.CataErased.base-z
d_base'45'z_490 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'z_490 = erased
-- Once.Adequacy.CataErased._.RelC
d_RelC_564 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelC_564 = erased
-- Once.Adequacy.CataErased._.LayerRel
d_LayerRel_574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny -> ()
d_LayerRel_574 = erased
-- Once.Adequacy.CataErased._.layer-rel
d_layer'45'rel_594
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CataErased._.layer-rel"
-- Once.Adequacy.CataErased._.evalᴰ-Cata-erased
d_eval'7472''45'Cata'45'erased_612 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'Cata'45'erased_612 = erased
-- Once.Adequacy.CataErased._._.mir'
d_mir''_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_mir''_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_mir''_630 v5
du_mir''_630 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_mir''_630 v0 = coe v0
-- Once.Adequacy.CataErased._._.w'
d_w''_634 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_w''_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_w''_634 v7
du_w''_634 ::
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_w''_634 v0 = coe v0
-- Once.Adequacy.CataErased._._.seed-eq
d_seed'45'eq_638 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'eq_638 = erased
-- Once.Adequacy.CataErased._._.goal
d_goal_646 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_646 = erased
-- Once.Adequacy.CataErased._._._.dalg_L
d_dalg_L_654 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dalg_L_654 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9
  = du_dalg_L_654 v0 v1 v2 v3 v5 v6 v9
du_dalg_L_654 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dalg_L_654 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) (coe v4)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
-- Once.Adequacy.CataErased._._._.algL
d_algL_660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algL_660 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_algL_660 v0 v1 v2 v3 v4 v5 v6 v9
du_algL_660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algL_660 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
      (coe
         du_dalg_L_654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
         (coe v6))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v2)
               (coe v4)))
         (coe v7))
-- Once.Adequacy.CataErased._._._.algL'
d_algL''_664 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algL''_664 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_algL''_664 v0 v1 v2 v3 v4 v5 v6 v9
du_algL''_664 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algL''_664 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_algL_660 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7)
-- Once.Adequacy.CataErased._._._.algM
d_algM_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algM_670 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_algM_670 v0 v1 v2 v3 v4 v5 v6 v9
du_algM_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algM_670 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe v2)
      (coe
         (\ v8 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_340
              (coe v0)
              (coe
                 MAlonzo.Code.Once.Type.C__'42'__122 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2) (coe v1)))
              (coe v1) (coe v5)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v8))))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v2) (coe v4) (coe v7))
-- Once.Adequacy.CataErased._._._.Lr≡
d_Lr'8801'_678 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Lr'8801'_678 = erased
-- Once.Adequacy.CataErased._._._.from-subst-eq
d_from'45'subst'45'eq_684 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'subst'45'eq_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12
  = du_from'45'subst'45'eq_684
du_from'45'subst'45'eq_684 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'subst'45'eq_684
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.CataErased._._._.algR-full
d_algR'45'full_700 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR'45'full_700 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_algR'45'full_700 v2 v4 v9
du_algR'45'full_700 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR'45'full_700 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_594
      (coe du_mL_712 (coe v0) (coe v1) (coe v2))
      (coe (\ v3 v4 -> coe du_from'45'subst'45'eq_684))
-- Once.Adequacy.CataErased._._._._.mL
d_mL_712 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mL_712 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_mL_712 v2 v4 v9
du_mL_712 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mL_712 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0)))
         (coe
            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v0)
               (coe v1)))
         (coe v2))
-- Once.Adequacy.CataErased._._._._.mM
d_mM_716 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mM_716 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_mM_716 v2 v4 v10
du_mM_716 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mM_716 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.CataErased._._._._.contL
d_contL_718 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contL_718 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contL_718 v0 v1 v2 v3 v5 v6 v12
du_contL_718 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contL_718 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_dalg_L_654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
         (coe v6))
-- Once.Adequacy.CataErased._._._._.contM
d_contM_722 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contM_722 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_contM_722 v0 v1 v2 v3 v5 v6 v12
du_contM_722 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contM_722 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_340 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122 (coe v3)
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2) (coe v1)))
      (coe v1) (coe v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
            (coe v2) (coe v6)))
-- Once.Adequacy.CataErased._._._._.step-eq
d_step'45'eq_728 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_728 = erased
-- Once.Adequacy.CataErased._._._.rc
d_rc_750 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rc_750 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_rc_750 v0 v1 v2 v3 v4 v5 v6 v7
du_rc_750 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rc_750 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
                       (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                          (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                             (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                          (coe
                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v2)
                                (coe v4)))
                          (coe v8))
                       v9))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 v0
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                             (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                             (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))))
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) v5
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
                                   (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                            (coe v2) (coe v4)))
                                      (coe v8))
                                   v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v9
                          (coe
                             MAlonzo.Code.Data.List.Base.du_foldr_216
                             (coe (\ v10 v11 -> addInt (coe (1 :: Integer)) (coe v11)))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
                                   (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                            (coe v2) (coe v4)))
                                      (coe v8))
                                   v9)))))))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 v0
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                          (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))))
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) v5
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                             (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
                                (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                   (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                (coe
                                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v2)
                                         (coe v4)))
                                   (coe v8))
                                v9))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v9
                       (coe
                          MAlonzo.Code.Data.List.Base.du_length_268
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164
                                (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                   (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                (coe
                                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                   (coe
                                      MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                      (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46 (coe v2)
                                         (coe v4)))
                                   (coe v8))
                                v9))))))))
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 v2
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe v2) (coe v4) (coe v8))
                       v9))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (let v10
                           = MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.IRTy.C__'42'__20
                                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                                  (coe
                                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2)
                                        (coe v1))))
                               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) (coe v5)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 v2
                                           (coe
                                              MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                              (coe v2) (coe v4) (coe v8))
                                           v9)))) in
                     coe
                       (coe
                          v10
                          (coe
                             MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v9
                             (coe
                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                (coe (\ v11 v12 -> addInt (coe (1 :: Integer)) (coe v12)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 v2
                                      (coe
                                         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                         (coe v2) (coe v4) (coe v8))
                                      v9))))))))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (let v10
                        = MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                            (coe v0)
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                               (coe
                                  MAlonzo.Code.Once.Type.C__'42'__122 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2)
                                     (coe v1))))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) (coe v5)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_722
                                  (coe v2)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 v2
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                           (coe v2) (coe v4) (coe v8))
                                        v9)))) in
                  coe
                    (coe
                       v10
                       (coe
                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v9
                          (coe
                             MAlonzo.Code.Data.List.Base.du_length_268
                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_164 v2
                                   (coe
                                      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                      (coe v2) (coe v4) (coe v8))
                                   v9)))))))))
      (\ v8 v9 v10 -> coe du_algR'45'full_700 (coe v2) (coe v4) v8)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_462
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2)) (coe v7))
-- Once.Adequacy.CataErased.push-⊎₁'
d_push'45''8846''8321'''_778 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'''_778 = erased
-- Once.Adequacy.CataErased.push-⊎₂'
d_push'45''8846''8322'''_800 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'''_800 = erased
-- Once.Adequacy.CataErased.push-×'
d_push'45''215'''_826 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'''_826 = erased
-- Once.Adequacy.CataErased.forget-coh
d_forget'45'coh_842 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'coh_842 = erased
-- Once.Adequacy.CataErased.liftFn-SigOp
d_liftFn'45'SigOp_930 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'SigOp_930 = erased
