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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_16 ::
  Integer ->
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_16 = erased
-- Once.Functor.Translate.Base-irrelevant
d_Base'45'irrelevant_78 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Base'45'irrelevant_78 = erased
-- Once.Functor.Translate._.uip
d_uip_98 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uip_98 = erased
-- Once.Functor.Translate.IsConcrete-irrelevant
d_IsConcrete'45'irrelevant_122 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsConcrete'45'irrelevant_122 = erased
-- Once.Functor.Translate.WFFun-irrelevant
d_WFFun'45'irrelevant_158 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WFFun'45'irrelevant_158 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_180 :: MAlonzo.Code.Once.Spec.Type.T_WFFun_118
d_wf'45'NatF_180
  = coe
      MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134
      (coe
         MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126
         (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94))
      (coe MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128)
