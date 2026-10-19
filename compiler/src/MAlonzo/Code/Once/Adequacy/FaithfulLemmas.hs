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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Adequacy.CataErased
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.StreamInf
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.FaithfulLemmas.≡ˢ
d_'8801''738'_52 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''738'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8801''738'_52 v9
du_'8801''738'_52 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''738'_52 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas.subst-T-return∞
d_subst'45'T'45'return'8734'_66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'return'8734'_66 = erased
-- Once.Adequacy.FaithfulLemmas.subst-arrow
d_subst'45'arrow_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arrow_94 = erased
-- Once.Adequacy.FaithfulLemmas.RelS-substˡ⁻
d_RelS'45'subst'737''8315'_118 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'subst'737''8315'_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_RelS'45'subst'737''8315'_118 v9
du_RelS'45'subst'737''8315'_118 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'subst'737''8315'_118 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas.RelS-substF
d_RelS'45'substF_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'substF_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_RelS'45'substF_146 v11
du_RelS'45'substF_146 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'substF_146 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas.RelS-substF₀
d_RelS'45'substF'8320'_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'substF'8320'_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_RelS'45'substF'8320'_176 v11
du_RelS'45'substF'8320'_176 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'substF'8320'_176 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas.evalᴰ-subst-cod
d_eval'7472''45'subst'45'cod_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'7472''45'subst'45'cod_198 = erased
-- Once.Adequacy.FaithfulLemmas.coerce-ν-in-subst
d_coerce'45'ν'45'in'45'subst_218 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'subst_218 = erased
-- Once.Adequacy.FaithfulLemmas.ana-erase
d_ana'45'erase_252 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'erase_252 = erased
-- Once.Adequacy.FaithfulLemmas.apply-rel
d_apply'45'rel_272 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_apply'45'rel_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_apply'45'rel_272 v7 v8 v9 v10
du_apply'45'rel_272 ::
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_apply'45'rel_272 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe v2 v0 v1 v3)
-- Once.Adequacy.FaithfulLemmas._.AB
d_AB_296 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_AB_296 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_AB_296 v2 v3 v4
du_AB_296 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_AB_296 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))
      (coe v1)
-- Once.Adequacy.FaithfulLemmas.cataM-fold
d_cataM'45'fold_328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cataM'45'fold_328 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         (\ v9 v10 v11 ->
            MAlonzo.Code.Once.Adequacy.CataErased.d_cata'45'erased'45'rel_892
              (coe v0) (coe v1) (coe v3) (coe v2)
              (coe du_Arr_348 (coe v2) (coe v3) (coe v4)) (coe v5)
              (coe du_applyIR_354 (coe v2) (coe v3)) (coe v6)
              (coe
                 (\ v12 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                      (coe MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70 (coe v7))
                      (coe (\ v13 -> coe v13 v12))))
              (coe
                 (\ v12 v13 v14 ->
                    coe
                      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                      (coe du_apply'45'rel_272 (coe v12) (coe v13) (coe v8) (coe v14))))
              (coe v9)))
-- Once.Adequacy.FaithfulLemmas._.Arr
d_Arr_348 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Arr_348 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 = du_Arr_348 v2 v3 v4
du_Arr_348 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Arr_348 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
      (coe
         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
         (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))
      (coe v1)
-- Once.Adequacy.FaithfulLemmas._.c₀
d_c'8320'_350 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_c'8320'_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_c'8320'_350 v6
du_c'8320'_350 ::
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_c'8320'_350 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.applyIR
d_applyIR_354 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_applyIR_354 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_applyIR_354 v2 v3
du_applyIR_354 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_applyIR_354 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                  (coe v1)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
               (coe v1))))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe MAlonzo.Code.Once.IR.C_fst_42)
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.FaithfulLemmas._.innerCata
d_innerCata_356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_innerCata_356 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_innerCata_356 v2 v3 v5
du_innerCata_356 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_innerCata_356 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_Cata_106
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v2))
      (coe du_applyIR_354 (coe v0) (coe v1))
-- Once.Adequacy.FaithfulLemmas.cata-body
d_cata'45'body_404 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'body_404 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3) (coe v4))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v2)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
                     (coe v6))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                  (coe v6))
               (coe v9))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                  (coe v4))))
         (coe v10))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe v9) (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
            (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
               (coe v4))
            (coe v11)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
            (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v5))
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_cataM_364 (coe v5) (coe v6)
            (coe v8)))
      (coe
         (\ v13 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 (coe v5) (coe v8)
                 (coe
                    MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                    (coe v5) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70 (coe v13))))))
      (coe v12)
      (coe
         d_cataM'45'fold_328 (coe v0) (coe v1) (coe v5) (coe v6) (coe v7)
         (coe v8))
-- Once.Adequacy.FaithfulLemmas.anaM-unfold
d_anaM'45'unfold_444 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_anaM'45'unfold_444 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_anaM'45'unfold_444 v0 v1 v2 v3 v5 v6 v7 v8 v9
du_anaM'45'unfold_444 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_anaM'45'unfold_444 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
              (coe
                 du_stream_612 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                 (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))))
-- Once.Adequacy.FaithfulLemmas._.Arr
d_Arr_466 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Arr_466 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_Arr_466 v2 v3 v5
du_Arr_466 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Arr_466 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v2)))
      (coe
         MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
         (coe v1))
-- Once.Adequacy.FaithfulLemmas._.H
d_H_468 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_H_468 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_H_468 v2
du_H_468 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_H_468 v0
  = coe
      MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0)
-- Once.Adequacy.FaithfulLemmas._.H₁
d_H'8321'_470 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_H'8321'_470 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_H'8321'_470 v2
du_H'8321'_470 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_H'8321'_470 v0
  = coe
      MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
         (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v0)))
-- Once.Adequacy.FaithfulLemmas._.c₀
d_c'8320'_472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_c'8320'_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_c'8320'_472 v7
du_c'8320'_472 ::
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_c'8320'_472 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.applyIR
d_applyIR_476 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_applyIR_476 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_applyIR_476 v2 v3
du_applyIR_476 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_applyIR_476 v0 v1
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
                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                  (coe v1))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe MAlonzo.Code.Once.IR.C_fst_42)
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.FaithfulLemmas._.coalg'
d_coalg''_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_coalg''_478 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_coalg''_478 v2 v3
du_coalg''_478 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_coalg''_478 v0 v1 = coe du_applyIR_476 (coe v0) (coe v1)
-- Once.Adequacy.FaithfulLemmas._.Ana-IR
d_Ana'45'IR_482 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_Ana'45'IR_482 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_Ana'45'IR_482 v2 v3 v6
du_Ana'45'IR_482 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_Ana'45'IR_482 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_Ana_122
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v2))
      (coe du_coalg''_478 (coe v0) (coe v1))
-- Once.Adequacy.FaithfulLemmas._.seedOf
d_seedOf_484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny
d_seedOf_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_seedOf_484 v10
du_seedOf_484 :: AgdaAny -> AgdaAny
du_seedOf_484 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.f₂
d_f'8322'_490 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny
d_f'8322'_490 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_f'8322'_490 v2 v6 v10
du_f'8322'_490 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_f'8322'_490 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
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
-- Once.Adequacy.FaithfulLemmas._.cE
d_cE_496 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_cE_496 v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 v10
  = du_cE_496 v0 v1 v2 v3 v5 v6 v7 v10
du_cE_496 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_cE_496 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
      (coe du_f'8322'_490 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe du_Arr_466 (coe v2) (coe v3) (coe v4)))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
         (coe du_coalg''_478 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7)))
-- Once.Adequacy.FaithfulLemmas._.c₁
d_c'8321'_500 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_c'8321'_500 v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 v10
  = du_c'8321'_500 v0 v1 v2 v3 v5 v6 v7 v10
du_c'8321'_500 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_c'8321'_500 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
      (coe
         MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2)))
         erased)
      (coe
         du_cE_496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.Adequacy.FaithfulLemmas._.c₂
d_c'8322'_508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_c'8322'_508 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10
  = du_c'8322'_508 v2 v6 v8 v10
du_c'8322'_508 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_c'8322'_508 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
      (coe
         MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased)
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
            (coe v0) (coe v1))
         (coe v2 v3))
-- Once.Adequacy.FaithfulLemmas._.layer
d_layer_522 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_layer_522 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_layer_522 v2 v6 v10 v11 v12
du_layer_522 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_layer_522 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_cμin'45'rel_1246 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
         (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
         (coe v0) (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'45'rel_1112 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.FaithfulLemmas._.R₄
d_R'8324'_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> ()
d_R'8324'_542 = erased
-- Once.Adequacy.FaithfulLemmas._.R₃
d_R'8323'_552 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> ()
d_R'8323'_552 = erased
-- Once.Adequacy.FaithfulLemmas._.hc
d_hc_568 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_hc_568 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_hc_568 v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v11 v12
du_hc_568 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_hc_568 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
      (coe
         du_cE_496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v9))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
            (coe v2) (coe v5))
         (coe v7 v10))
      (coe
         MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
         (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2)))
         erased)
      (coe
         MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased)
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
            (coe v1)
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe du_Arr_466 (coe v2) (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
            (coe
               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
               (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
            (coe du_coalg''_478 (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v9)))
         (coe v7 v10) (coe du_f'8322'_490 (coe v2) (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
            (coe v2) (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'mono_464
            (coe
               (\ v12 v13 v14 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v14))))
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                     (coe du_Arr_466 (coe v2) (coe v3) (coe v4)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v2)
                     (coe v3)))
               (coe du_applyIR_476 (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v9)))
            (coe v7 v10)
            (coe du_apply'45'rel_272 (coe v9) (coe v10) (coe v8) (coe v11)))
         (coe
            (\ v12 v13 v14 ->
               case coe v14 of
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                   -> case coe v16 of
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                          -> coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe v18))))
                        _ -> MAlonzo.RTE.mazUnreachableError
                 _ -> MAlonzo.RTE.mazUnreachableError)))
      (coe
         (\ v12 v13 v14 ->
            case coe v14 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                -> case coe v16 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                       -> case coe v18 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                              -> case coe v20 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                     -> coe
                                          du_layer_522 (coe v2) (coe v5) (coe v15) (coe v17)
                                          (coe v22)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.FaithfulLemmas._.stream
d_stream_612 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_stream_612 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_stream_612 v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v11 v12
du_stream_612 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
du_stream_612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_ana'7477''45'rel_1422
      (coe du_H_468 (coe v2))
      (coe
         du_c'8321'_500 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6))
      (coe
         (\ v12 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased)
              (coe
                 MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v2) (coe v5))
                 (coe v7 v12))))
      (coe
         du_hc_568 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
      (coe v9) (coe v10) (coe v11)
-- Once.Adequacy.FaithfulLemmas.ana-body
d_ana'45'body_662 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ana'45'body_662 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v8)))
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6)))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3) (coe v4))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v2)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v8)))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
                     (coe v6)))
               (coe v10))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                  (coe v4))))
         (coe v11))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v8)))
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6)))
         (coe v10) (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
            (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
               (coe v4))
            (coe v12)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v8)))
            (coe
               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v5)
               (coe v6)))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v5) (coe v8)))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_anaM_382 (coe v5) (coe v6)
            (coe v9)))
      (coe
         (\ v14 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
              (coe
                 (\ v15 ->
                    coe
                      MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                      (coe
                         MAlonzo.Code.Once.Lang.StreamInf.du_anaF'7477'_150 v5
                         (\ v16 ->
                            coe
                              MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                              (coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                 (coe v5) (coe v9))
                              (coe v14 v16))
                         v15)))))
      (coe v13)
      (coe
         du_anaM'45'unfold_444 (coe v0) (coe v1) (coe v5) (coe v6) (coe v8)
         (coe v9))
-- Once.Adequacy.FaithfulLemmas.loopM-iter
d_loopM'45'iter_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_loopM'45'iter_694 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
      (coe
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'iter'8734'_622
              (coe
                 (\ v10 ->
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                      (coe v0) (coe v1)
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe du_Arr_710 (coe v2) (coe v3)))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'43'__22
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)))
                      (coe du_applyIR_722 (coe v2) (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v10))))
              (coe v5) (coe (\ v10 v11 v12 -> v12))
              (coe du_s'45'inr_786 (coe v6)) (coe v7) (coe v8) (coe v9)))
-- Once.Adequacy.FaithfulLemmas._.Arr
d_Arr_710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_Arr_710 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 = du_Arr_710 v2 v3
du_Arr_710 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_Arr_710 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
      (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v1) (coe v0))
-- Once.Adequacy.FaithfulLemmas._.QA
d_QA_712 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_QA_712 = erased
-- Once.Adequacy.FaithfulLemmas._.QB
d_QB_714 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_QB_714 = erased
-- Once.Adequacy.FaithfulLemmas._.QBA
d_QBA_716 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_QBA_716 = erased
-- Once.Adequacy.FaithfulLemmas._.c₀
d_c'8320'_718 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_c'8320'_718 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_c'8320'_718 v4
du_c'8320'_718 ::
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_c'8320'_718 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.applyIR
d_applyIR_722 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.IR.T_IR_16
d_applyIR_722 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 = du_applyIR_722 v2 v3
du_applyIR_722 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_applyIR_722 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe MAlonzo.Code.Once.IR.C_fst_42)
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Adequacy.FaithfulLemmas._.s-inl
d_s'45'inl_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_s'45'inl_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_s'45'inl_732 v9
du_s'45'inl_732 :: AgdaAny -> AgdaAny
du_s'45'inl_732 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas._.s-lr
d_s'45'lr_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_s'45'lr_748 = erased
-- Once.Adequacy.FaithfulLemmas._.s-rl
d_s'45'rl_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_s'45'rl_764 = erased
-- Once.Adequacy.FaithfulLemmas._.s-inr
d_s'45'inr_786 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_s'45'inr_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_s'45'inr_786 v6 v7 v8 v9
du_s'45'inr_786 ::
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_s'45'inr_786 v0 v1 v2 v3
  = coe du_apply'45'rel_272 (coe v1) (coe v2) (coe v0) (coe v3)
-- Once.Adequacy.FaithfulLemmas._.start
d_start_812 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_start_812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_start_812 v9
du_start_812 :: AgdaAny -> AgdaAny
du_start_812 v0 = coe v0
-- Once.Adequacy.FaithfulLemmas.loop-body
d_loop'45'body_868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_loop'45'body_868 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v6) (coe v5)))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v3) (coe v4))))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_410 (coe v2)
               (coe v3) (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                  (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v6) (coe v5)))
               (coe v7))
            (coe
               MAlonzo.Code.Once.Surface.Elaborate.du_restrictEnv_84 (coe v3)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
               (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                  (coe v4))))
         (coe v8))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v6) (coe v5)))
         (coe v7) (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.SourceDenote.d_internalDefs_90
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v3)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
            (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
               (coe v4))
            (coe v9)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
            (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v6) (coe v5)))
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
            (coe v6))
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_loopM_398 (coe v5)
            (coe v6)))
      (coe
         (\ v11 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Lang.Iterative.du_iter'8734'_256 (coe v11))))
      (coe v10)
      (coe d_loopM'45'iter_694 (coe v0) (coe v1) (coe v5) (coe v6))
