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
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataErased.RelRes-of-mapRes
d_RelRes'45'of'45'mapRes_22 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126
d_RelRes'45'of'45'mapRes_22 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_RelRes'45'of'45'mapRes_22 v4
du_RelRes'45'of'45'mapRes_22 ::
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126
du_RelRes'45'of'45'mapRes_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Once.Res.C_rel'45'stopped_134
      MAlonzo.Code.Once.Res.C_returns_12 v1
        -> coe MAlonzo.Code.Once.Res.C_rel'45'returns_140 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataErased.mapRes-of-RelRes
d_mapRes'45'of'45'RelRes_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Res.T_Res'45'rel_126 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapRes'45'of'45'RelRes_44 = erased
-- Once.Adequacy.CataErased.T-ext
d_T'45'ext_64 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'ext_64 = erased
-- Once.Adequacy.CataErased.subst-T-stoppedT
d_subst'45'T'45'stoppedT_86 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'stoppedT_86 = erased
-- Once.Adequacy.CataErased.subst-T-resT
d_subst'45'T'45'resT_102 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'resT_102 = erased
-- Once.Adequacy.CataErased.subst-T-projTrace
d_subst'45'T'45'projTrace_116 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'projTrace_116 = erased
-- Once.Adequacy.CataErased.subst-Returns
d_subst'45'Returns_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  AgdaAny -> AgdaAny
d_subst'45'Returns_130 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_subst'45'Returns_130 v5
du_subst'45'Returns_130 :: AgdaAny -> AgdaAny
du_subst'45'Returns_130 v0 = coe v0
-- Once.Adequacy.CataErased.subst-T-valueT
d_subst'45'T'45'valueT_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'valueT_150 = erased
-- Once.Adequacy.CataErased.subst-cong-μS
d_subst'45'cong'45'μS_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'cong'45'μS_168 = erased
-- Once.Adequacy.CataErased.cataS-subst-functor
d_cataS'45'subst'45'functor_188 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'subst'45'functor_188 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom
d_eval'7472''45'subst'45'dom_208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom_208 = erased
-- Once.Adequacy.CataErased.evalᴰ-subst-dom-pair
d_eval'7472''45'subst'45'dom'45'pair_232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'dom'45'pair_232 = erased
-- Once.Adequacy.CataErased.pairᴰ-subst⁻
d_pair'7472''45'subst'8315'_266 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'7472''45'subst'8315'_266 = erased
-- Once.Adequacy.CataErased.cata-ev-algᴰ-is-D
d_cata'45'ev'45'alg'7472''45'is'45'D_286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'ev'45'alg'7472''45'is'45'D_286 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₁
d_subst'45'S'8853''45'inj'8321'_314 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8321'_314 = erased
-- Once.Adequacy.CataErased.subst-S⊕-inj₂
d_subst'45'S'8853''45'inj'8322'_338 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'S'8853''45'inj'8322'_338 = erased
-- Once.Adequacy.CataErased.subst-S⊗
d_subst'45'S'8855'_366 ::
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
d_subst'45'S'8855'_366 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₁
d_push'7472''7477''45''43''8321'_386 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8321'_386 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-+₂
d_push'7472''7477''45''43''8322'_404 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''43''8322'_404 = erased
-- Once.Adequacy.CataErased.pushᴰᴵ-*
d_push'7472''7477''45''42'_424 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''7477''45''42'_424 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₁
d_push'7472''45''43''8321'_444 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8321'_444 = erased
-- Once.Adequacy.CataErased.pushᴰ-+₂
d_push'7472''45''43''8322'_462 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''43''8322'_462 = erased
-- Once.Adequacy.CataErased.pushᴰ-*
d_push'7472''45''42'_482 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7472''45''42'_482 = erased
-- Once.Adequacy.CataErased.push-⊎₁
d_push'45''8846''8321'_506 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'_506 = erased
-- Once.Adequacy.CataErased.push-⊎₂
d_push'45''8846''8322'_528 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'_528 = erased
-- Once.Adequacy.CataErased.push-×
d_push'45''215'_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'_554 = erased
-- Once.Adequacy.CataErased.subst-SK
d_subst'45'SK_574 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'SK_574 = erased
-- Once.Adequacy.CataErased.base-z
d_base'45'z_588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'z_588 = erased
-- Once.Adequacy.CataErased._.RelC
d_RelC_662 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 -> ()
d_RelC_662 = erased
-- Once.Adequacy.CataErased._.LayerRel
d_LayerRel_672 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny -> ()
d_LayerRel_672 = erased
-- Once.Adequacy.CataErased._.layer-rel
d_layer'45'rel_692
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CataErased._.layer-rel"
-- Once.Adequacy.CataErased._.evalᴰ-Cata-erased
d_eval'7472''45'Cata'45'erased_710 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'Cata'45'erased_710 = erased
-- Once.Adequacy.CataErased._._.mir'
d_mir''_728 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_mir''_728 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_mir''_728 v5
du_mir''_728 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_mir''_728 v0 = coe v0
-- Once.Adequacy.CataErased._._.w'
d_w''_732 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_w''_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_w''_732 v7
du_w''_732 ::
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_w''_732 v0 = coe v0
-- Once.Adequacy.CataErased._._.seed-eq
d_seed'45'eq_736 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seed'45'eq_736 = erased
-- Once.Adequacy.CataErased._._.body
d_body_742 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_742 = erased
-- Once.Adequacy.CataErased._._._.dalg_L
d_dalg_L_748 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_dalg_L_748 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8
  = du_dalg_L_748 v0 v1 v2 v3 v5 v6 v8
du_dalg_L_748 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_dalg_L_748 v0 v1 v2 v3 v4 v5 v6
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
d_algL_754 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_algL_754 v0 v1 v2 v3 v4 v5 v6 ~v7 v8
  = du_algL_754 v0 v1 v2 v3 v4 v5 v6 v8
du_algL_754 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_algL_754 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
      (coe
         du_dalg_L_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
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
d_algL''_758 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_algL''_758 v0 v1 v2 v3 v4 v5 v6 ~v7 v8
  = du_algL''_758 v0 v1 v2 v3 v4 v5 v6 v8
du_algL''_758 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_algL''_758 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_algL_754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7)
-- Once.Adequacy.CataErased._._._.algM
d_algM_764 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_algM_764 v0 v1 v2 v3 v4 v5 v6 ~v7 v8
  = du_algM_764 v0 v1 v2 v3 v4 v5 v6 v8
du_algM_764 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_algM_764 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
      (coe v2)
      (coe
         (\ v8 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_260
              (coe v0)
              (coe
                 MAlonzo.Code.Once.Type.C__'42'__122 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2) (coe v1)))
              (coe v1) (coe v5)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v8))))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v2) (coe v4) (coe v7))
-- Once.Adequacy.CataErased._._._.Lr≡
d_Lr'8801'_772 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Lr'8801'_772 = erased
-- Once.Adequacy.CataErased._._._.from-subst-eq
d_from'45'subst'45'eq_778 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'45'subst'45'eq_778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                          ~v10 ~v11
  = du_from'45'subst'45'eq_778 v8
du_from'45'subst'45'eq_778 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'45'subst'45'eq_778 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         du_RelRes'45'of'45'mapRes_22
         (coe MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20 (coe v0)))
-- Once.Adequacy.CataErased._._._.to-subst-eq
d_to'45'subst'45'eq_794 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'45'subst'45'eq_794 = erased
-- Once.Adequacy.CataErased._._._.algR-full
d_algR'45'full_808 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR'45'full_808 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 ~v10
  = du_algR'45'full_808 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_algR'45'full_808 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR'45'full_808 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_946
      (coe du_mL_820 (coe v2) (coe v4) (coe v7))
      (coe du_mM_824 (coe v2) (coe v4) (coe v8))
      (coe
         (\ v9 v10 v11 v12 v13 ->
            coe
              du_from'45'subst'45'eq_778
              (coe
                 du_contL_826 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                 (coe v9))))
-- Once.Adequacy.CataErased._._._._.mL
d_mL_820 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_mL_820 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_mL_820 v2 v4 v8
du_mL_820 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_mL_820 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196
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
d_mM_824 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_mM_824 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_mM_824 v2 v4 v9
du_mM_824 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_mM_824 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.CataErased._._._._.contL
d_contL_826 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_contL_826 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_contL_826 v0 v1 v2 v3 v5 v6 v11
du_contL_826 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_contL_826 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_dalg_L_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
         (coe v6))
-- Once.Adequacy.CataErased._._._._.contM
d_contM_830 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_contM_830 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_contM_830 v0 v1 v2 v3 v5 v6 v11
du_contM_830 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_contM_830 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_260 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122 (coe v3)
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2) (coe v1)))
      (coe v1) (coe v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
            (coe v2) (coe v6)))
-- Once.Adequacy.CataErased._._._._.step-eq
d_step'45'eq_838 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
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
d_step'45'eq_838 = erased
-- Once.Adequacy.CataErased._._._.rc
d_rc_868 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rc_868 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
              (coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_bindRes_52
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
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
                             (coe v8))))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
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
                             (coe v8))))
                    (coe
                       (\ v9 ->
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                            (coe v0)
                            (coe
                               MAlonzo.Code.Once.IRTy.C__'42'__20
                               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84
                                  (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2))
                                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) (coe v5)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
                                  (coe
                                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624
                                     (coe MAlonzo.Code.Once.IRTy.d_eraseF_54 (coe v2)))
                                  (coe v9)))))))
              (coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                 (coe
                    du_algL''_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v8)))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
              (coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_bindRes_52
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                             (coe v2) (coe v4) (coe v8))))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_196 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                             (coe v2) (coe v4) (coe v8))))
                    (coe
                       (\ v9 ->
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                            (coe v0)
                            (coe
                               MAlonzo.Code.Once.IRTy.C__'42'__20
                               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                  (coe
                                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2)
                                     (coe v1))))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)) (coe v5)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_770
                                  (coe v2) (coe v9)))))))
              (coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                 (coe
                    du_algM_764 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v8)))))
      (\ v8 v9 v10 ->
         coe
           du_algR'45'full_808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
           (coe v5) (coe v6) v8 v9)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2)) (coe v7))
-- Once.Adequacy.CataErased.push-⊎₁'
d_push'45''8846''8321'''_890 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8321'''_890 = erased
-- Once.Adequacy.CataErased.push-⊎₂'
d_push'45''8846''8322'''_912 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846''8322'''_912 = erased
-- Once.Adequacy.CataErased.push-×'
d_push'45''215'''_938 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'''_938 = erased
-- Once.Adequacy.CataErased.forget-coh
d_forget'45'coh_954 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'coh_954 = erased
-- Once.Adequacy.CataErased.liftFn-SigOp
d_liftFn'45'SigOp_1042 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'SigOp_1042 = erased
