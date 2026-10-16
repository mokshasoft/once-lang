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
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed

-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_14 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_14 = erased
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_72 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_72 = erased
-- Once.Functor.Translate.IsConcrete-irrelevant
d_IsConcrete'45'irrelevant_96 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsConcrete'45'irrelevant_96 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_128 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_128 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_150 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48
d_wf'45'NatF_150
  = coe
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60
      (coe
         MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52
         (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10))
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54)
