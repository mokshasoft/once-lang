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

module MAlonzo.Code.Once.Adequacy.CoerceFaithful where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Surface.CoerceIR
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CoerceFaithful.bind-ret
d_bind'45'ret_50 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind'45'ret_50 = erased
-- Once.Adequacy.CoerceFaithful.fmapT-subst
d_fmapT'45'subst_64 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapT'45'subst_64 = erased
-- Once.Adequacy.CoerceFaithful.subst-T-∘
d_subst'45'T'45''8728'_80 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45''8728'_80 = erased
-- Once.Adequacy.CoerceFaithful.subst-⟦⟧
d_subst'45''10214''10215'_94 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''10214''10215'_94 = erased
-- Once.Adequacy.CoerceFaithful.eval-subst
d_eval'45'subst_112 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'subst_112 = erased
-- Once.Adequacy.CoerceFaithful.uip
d_uip_126 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uip_126 = erased
-- Once.Adequacy.CoerceFaithful.sym-sym
d_sym'45'sym_134 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'sym_134 = erased
-- Once.Adequacy.CoerceFaithful.subst-arr
d_subst'45'arr_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arr_156 = erased
-- Once.Adequacy.CoerceFaithful.subst-arr₀
d_subst'45'arr'8320'_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arr'8320'_172 = erased
-- Once.Adequacy.CoerceFaithful.subst-pair
d_subst'45'pair_192 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'pair_192 = erased
-- Once.Adequacy.CoerceFaithful.subst-inj₁
d_subst'45'inj'8321'_212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'inj'8321'_212 = erased
-- Once.Adequacy.CoerceFaithful.subst-inj₂
d_subst'45'inj'8322'_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'inj'8322'_230 = erased
-- Once.Adequacy.CoerceFaithful.liftFn-apply₁
d_liftFn'45'apply'8321'_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'apply'8321'_242 = erased
-- Once.Adequacy.CoerceFaithful.liftFn-curry₁
d_liftFn'45'curry'8321'_264 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'curry'8321'_264 = erased
-- Once.Adequacy.CoerceFaithful.apply-red₀
d_apply'45'red'8320'_288 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'red'8320'_288 = erased
-- Once.Adequacy.CoerceFaithful.curry-red₀
d_curry'45'red'8320'_314 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'red'8320'_314 = erased
-- Once.Adequacy.CoerceFaithful.liftFn-apply₀
d_liftFn'45'apply'8320'_328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'apply'8320'_328 = erased
-- Once.Adequacy.CoerceFaithful.liftFn-curry₀
d_liftFn'45'curry'8320'_350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_liftFn'45'curry'8320'_350 = erased
-- Once.Adequacy.CoerceFaithful.coeIR-lift
d_coeIR'45'lift_370 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coeIR'45'lift_370 = erased
-- Once.Adequacy.CoerceFaithful.arr₀
d_arr'8320'_390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'8320'_390 = erased
-- Once.Adequacy.CoerceFaithful.arr₁
d_arr'8321'_410 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arr'8321'_410 = erased
-- Once.Adequacy.CoerceFaithful.arrω
d_arrω_430 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arrω_430 = erased
-- Once.Adequacy.CoerceFaithful._.l
d_l_552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_l_552 = erased
-- Once.Adequacy.CoerceFaithful._.r
d_r_560 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r_560 = erased
-- Once.Adequacy.CoerceFaithful._.AB
d_AB_666 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Once.Type.T_Type_108
d_AB_666 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 = du_AB_666 v1 v3 v5
du_AB_666 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_AB_666 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_One_8) (coe v2))
      (coe v1)
-- Once.Adequacy.CoerceFaithful._.arg
d_arg_668 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg_668 = erased
-- Once.Adequacy.CoerceFaithful._.pr
d_pr_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pr_676 = erased
-- Once.Adequacy.CoerceFaithful._.body
d_body_690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_690 = erased
-- Once.Adequacy.CoerceFaithful._.AB
d_AB_726 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Once.Type.T_Type_108
d_AB_726 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 = du_AB_726 v1 v3 v5
du_AB_726 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_AB_726 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
      (coe v1)
-- Once.Adequacy.CoerceFaithful._.arg
d_arg_728 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arg_728 = erased
-- Once.Adequacy.CoerceFaithful._.pr
d_pr_736 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pr_736 = erased
-- Once.Adequacy.CoerceFaithful._.body
d_body_750 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body_750 = erased
-- Once.Adequacy.CoerceFaithful.VfSem
d_VfSem_770 a0 a1 a2 a3 = ()
data T_VfSem_770 = C_constructor_790
-- Once.Adequacy.CoerceFaithful.VfSem.D
d_D_784 ::
  T_VfSem_770 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_D_784 = erased
-- Once.Adequacy.CoerceFaithful.VfSem.pt
d_pt_788 ::
  T_VfSem_770 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pt_788 = erased
-- Once.Adequacy.CoerceFaithful.vf-sem
d_vf'45'sem_798 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 -> T_VfSem_770
d_vf'45'sem_798 = erased
-- Once.Adequacy.CoerceFaithful..extendedlambda0
d_'46'extendedlambda0_890 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_890 = erased
-- Once.Adequacy.CoerceFaithful..extendedlambda0
d_'46'extendedlambda0_908 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_908 = erased
-- Once.Adequacy.CoerceFaithful.coerce-lift-yes
d_coerce'45'lift'45'yes_928 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'lift'45'yes_928 = erased
-- Once.Adequacy.CoerceFaithful._.E
d_E_948 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_948 = erased
-- Once.Adequacy.CoerceFaithful._.s
d_s_950 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> T_VfSem_770
d_s_950 = erased
-- Once.Adequacy.CoerceFaithful._.x₀
d_x'8320'_952 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_x'8320'_952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_x'8320'_952 v7
du_x'8320'_952 :: AgdaAny -> AgdaAny
du_x'8320'_952 v0 = coe v0
-- Once.Adequacy.CoerceFaithful._.m
d_m_954 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_m_954 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 = du_m_954 v0 v1 v2 v6 v7
du_m_954 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_m_954 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v2)) (coe v3)
      (coe v4)
-- Once.Adequacy.CoerceFaithful.coerce-lift-dec
d_coerce'45'lift'45'dec_972 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'lift'45'dec_972 = erased
-- Once.Adequacy.CoerceFaithful.coerce-lift
d_coerce'45'lift_1012 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'lift_1012 = erased
