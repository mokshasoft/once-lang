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
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Type

-- Once.Functor.Translate.⟦_⟧-base
d_'10214'_'10215''45'base_6 ::
  () -> MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''45'base_6 = erased
-- Once.Functor.Translate.translateF
d_translateF_38 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6
d_translateF_38 ~v0 v1 = du_translateF_38 v1
du_translateF_38 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6
du_translateF_38 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v1
        -> coe MAlonzo.Code.Once.Functor.Base.C_SK_8
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe MAlonzo.Code.Once.Functor.Base.C_SId_10
      MAlonzo.Code.Once.Type.C__'8853'__114 v1 v2
        -> coe
             MAlonzo.Code.Once.Functor.Base.C__S'8853'__12
             (coe du_translateF_38 (coe v1)) (coe du_translateF_38 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__116 v1 v2
        -> coe
             MAlonzo.Code.Once.Functor.Base.C__S'8855'__14
             (coe du_translateF_38 (coe v1)) (coe du_translateF_38 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Translate.μ-sem
d_μ'45'sem_58 :: () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_μ'45'sem_58 = erased
-- Once.Functor.Translate.ν-sem
d_ν'45'sem_64 :: () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_ν'45'sem_64 = erased
-- Once.Functor.Translate.⟦_⟧F-base
d_'10214'_'10215'F'45'base_70 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F'45'base_70 = erased
-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_104 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_104 = erased
-- Once.Functor.Translate.IsBaseType
d_IsBaseType_148 a0 = ()
data T_IsBaseType_148
  = C_base'45'Unit_150 | C_base'45'Void_152 | C_base'45'Int_154 |
    C_base'45'Float_156 | C_base'45'Str_158 | C_base'45'Buffer_160 |
    C_base'45'Prod_166 T_IsBaseType_148 T_IsBaseType_148 |
    C_base'45'Sum_172 T_IsBaseType_148 T_IsBaseType_148
-- Once.Functor.Translate.WellFormedF
d_WellFormedF_174 a0 = ()
data T_WellFormedF_174
  = C_wf'45'K_178 T_IsBaseType_148 | C_wf'45'Id_180 |
    C_wf'45'Sum_186 T_WellFormedF_174 T_WellFormedF_174 |
    C_wf'45'Prod_192 T_WellFormedF_174 T_WellFormedF_174
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_200 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_IsBaseType_148 ->
  T_IsBaseType_148 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_200 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_224 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  T_WellFormedF_174 ->
  T_WellFormedF_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_224 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_246 :: T_WellFormedF_174
d_wf'45'NatF_246
  = coe
      C_wf'45'Sum_186 (coe C_wf'45'K_178 (coe C_base'45'Unit_150))
      (coe C_wf'45'Id_180)
