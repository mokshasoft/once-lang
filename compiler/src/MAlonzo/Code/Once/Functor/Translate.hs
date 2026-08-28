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
d_translateF_60 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
d_translateF_60 ~v0 ~v1 v2 = du_translateF_60 v2
du_translateF_60 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
du_translateF_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v1
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SK_8
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe MAlonzo.Code.Once.Semantics.Functor.C_SId_10
      MAlonzo.Code.Once.Type.C__'8853'__114 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12
             (coe du_translateF_60 (coe v1)) (coe du_translateF_60 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__116 v1 v2
        -> coe
             MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14
             (coe du_translateF_60 (coe v1)) (coe du_translateF_60 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Translate.μ-sem
d_μ'45'sem_88 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_μ'45'sem_88 = erased
-- Once.Functor.Translate.ν-sem
d_ν'45'sem_96 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_ν'45'sem_96 = erased
-- Once.Functor.Translate.⟦_,_⟧F-base
d_'10214'_'44'_'10215'F'45'base_104 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'44'_'10215'F'45'base_104 = erased
-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_148 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_148 = erased
-- Once.Functor.Translate.IsBaseType
d_IsBaseType_200 a0 = ()
data T_IsBaseType_200
  = C_base'45'Unit_202 | C_base'45'Void_204 | C_base'45'Int_206 |
    C_base'45'Float_208 | C_base'45'Str_210 | C_base'45'Buffer_212 |
    C_base'45'Prod_218 T_IsBaseType_200 T_IsBaseType_200 |
    C_base'45'Sum_224 T_IsBaseType_200 T_IsBaseType_200
-- Once.Functor.Translate.IsConcrete
d_IsConcrete_226 a0 = ()
data T_IsConcrete_226
  = C_con'45'base_230 T_IsBaseType_200 |
    C_con'45'fun_238 T_IsBaseType_200 T_IsConcrete_226
-- Once.Functor.Translate.WellFormedF
d_WellFormedF_240 a0 = ()
data T_WellFormedF_240
  = C_wf'45'K_244 T_IsBaseType_200 | C_wf'45'Id_246 |
    C_wf'45'Sum_252 T_WellFormedF_240 T_WellFormedF_240 |
    C_wf'45'Prod_258 T_WellFormedF_240 T_WellFormedF_240
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_266 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_IsBaseType_200 ->
  T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_266 = erased
-- Once.Functor.Translate.IsConcrete-irrelevant
d_IsConcrete'45'irrelevant_290 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_IsConcrete_226 ->
  T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsConcrete'45'irrelevant_290 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_322 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  T_WellFormedF_240 ->
  T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_322 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_344 :: T_WellFormedF_240
d_wf'45'NatF_344
  = coe
      C_wf'45'Sum_252 (coe C_wf'45'K_244 (coe C_base'45'Unit_202))
      (coe C_wf'45'Id_246)
