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
import qualified MAlonzo.Code.Once.Type

-- Once.Functor.Translate.⟦_,_⟧-base
d_'10214'_'44'_'10215''45'base_6 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'44'_'10215''45'base_6 = erased
-- Once.Functor.Translate.translateF
d_translateF_56 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
d_translateF_56 ~v0 ~v1 v2 = du_translateF_56 v2
du_translateF_56 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
du_translateF_56 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SK_8
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SId_10
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Translate.μ-sem
d_μ'45'sem_84 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_μ'45'sem_84 = erased
-- Once.Functor.Translate.ν-sem
d_ν'45'sem_92 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_ν'45'sem_92 = erased
-- Once.Functor.Translate.⟦_,_⟧F-base
d_'10214'_'44'_'10215'F'45'base_100 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'44'_'10215'F'45'base_100 = erased
-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_144 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_144 = erased
-- Once.Functor.Translate.IsBaseType
d_IsBaseType_196 a0 = ()
data T_IsBaseType_196
  = C_base'45'Unit_198 | C_base'45'Void_200 | C_base'45'Int_202 |
    C_base'45'Float_204 |
    C_base'45'Prod_210 T_IsBaseType_196 T_IsBaseType_196 |
    C_base'45'Sum_216 T_IsBaseType_196 T_IsBaseType_196 |
    C_base'45'rigid_220
-- Once.Functor.Translate.IsConcrete
d_IsConcrete_222 a0 = ()
data T_IsConcrete_222
  = C_con'45'base_226 T_IsBaseType_196 |
    C_con'45'fun_234 T_IsBaseType_196 T_IsBaseType_196
-- Once.Functor.Translate.WellFormedF
d_WellFormedF_236 a0 = ()
data T_WellFormedF_236
  = C_wf'45'K_240 T_IsBaseType_196 | C_wf'45'Id_242 |
    C_wf'45'Sum_248 T_WellFormedF_236 T_WellFormedF_236 |
    C_wf'45'Prod_254 T_WellFormedF_236 T_WellFormedF_236
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_262 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_IsBaseType_196 ->
  T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_262 = erased
-- Once.Functor.Translate.IsConcrete-irrelevant
d_IsConcrete'45'irrelevant_286 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_IsConcrete_222 ->
  T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsConcrete'45'irrelevant_286 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_318 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  T_WellFormedF_236 ->
  T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_318 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_340 :: T_WellFormedF_236
d_wf'45'NatF_340
  = coe
      C_wf'45'Sum_248 (coe C_wf'45'K_240 (coe C_base'45'Unit_198))
      (coe C_wf'45'Id_242)
