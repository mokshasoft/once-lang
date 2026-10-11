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

module MAlonzo.Code.Once.Functor.Translate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed

-- Once.Functor.Translate.⟦_,_⟧-base
d_'10214'_'44'_'10215''45'base_6 ::
  () -> () -> MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_'10214'_'44'_'10215''45'base_6 = erased
-- Once.Functor.Translate.translateF
d_translateF_56 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
d_translateF_56 ~v0 ~v1 v2 = du_translateF_56 v2
du_translateF_56 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
du_translateF_56 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_12 v1
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SK_8
      MAlonzo.Code.Once.Spec.Type.C_Id_14
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SId_10
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Translate.μ-sem
d_μ'45'sem_84 ::
  () -> () -> MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> ()
d_μ'45'sem_84 = erased
-- Once.Functor.Translate.ν-sem
d_ν'45'sem_92 ::
  () -> () -> MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> ()
d_ν'45'sem_92 = erased
-- Once.Functor.Translate.⟦_,_⟧F-base
d_'10214'_'44'_'10215'F'45'base_100 ::
  () -> () -> MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> () -> ()
d_'10214'_'44'_'10215'F'45'base_100 = erased
-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_144 ::
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_144 = erased
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_202 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_202 = erased
-- Once.Functor.Translate.IsConcrete-irrelevant
d_IsConcrete'45'irrelevant_226 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsConcrete'45'irrelevant_226 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_258 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_258 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_280 ::
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
d_wf'45'NatF_280
  = coe
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60
      (coe
         MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52
         (coe MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10))
      (coe MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54)
