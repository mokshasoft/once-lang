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
  () -> MAlonzo.Code.Once.Type.T_Type_34 -> ()
d_'10214'_'10215''45'base_6 = erased
-- Once.Functor.Translate.translateF
d_translateF_42 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6
d_translateF_42 ~v0 v1 = du_translateF_42 v1
du_translateF_42 ::
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6
du_translateF_42 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_36 v1
        -> coe MAlonzo.Code.Once.Functor.Base.C_SK_8
      MAlonzo.Code.Once.Type.C_Id_38
        -> coe MAlonzo.Code.Once.Functor.Base.C_SId_10
      MAlonzo.Code.Once.Type.C__'8853'__40 v1 v2
        -> coe
             MAlonzo.Code.Once.Functor.Base.C__S'8853'__12
             (coe du_translateF_42 (coe v1)) (coe du_translateF_42 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Functor.Base.C__S'8855'__14
             (coe du_translateF_42 (coe v1)) (coe du_translateF_42 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Translate.μ-sem
d_μ'45'sem_62 :: () -> MAlonzo.Code.Once.Type.T_Functor_32 -> ()
d_μ'45'sem_62 = erased
-- Once.Functor.Translate.ν-sem
d_ν'45'sem_68 :: () -> MAlonzo.Code.Once.Type.T_Functor_32 -> ()
d_ν'45'sem_68 = erased
-- Once.Functor.Translate.⟦_⟧F-base
d_'10214'_'10215'F'45'base_74 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_32 -> () -> ()
d_'10214'_'10215'F'45'base_74 = erased
-- Once.Functor.Translate.translate-coherence
d_translate'45'coherence_108 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_translate'45'coherence_108 = erased
-- Once.Functor.Translate.IsBaseType
d_IsBaseType_152 a0 = ()
data T_IsBaseType_152
  = C_base'45'Unit_154 | C_base'45'Void_156 | C_base'45'Int_158 |
    C_base'45'Float_160 | C_base'45'Str_162 | C_base'45'Buffer_164 |
    C_base'45'Prod_170 T_IsBaseType_152 T_IsBaseType_152 |
    C_base'45'Sum_176 T_IsBaseType_152 T_IsBaseType_152
-- Once.Functor.Translate.WellFormedF
d_WellFormedF_178 a0 = ()
data T_WellFormedF_178
  = C_wf'45'K_182 T_IsBaseType_152 | C_wf'45'Id_184 |
    C_wf'45'Sum_190 T_WellFormedF_178 T_WellFormedF_178 |
    C_wf'45'Prod_196 T_WellFormedF_178 T_WellFormedF_178
-- Once.Functor.Translate.IsBaseType-irrelevant
d_IsBaseType'45'irrelevant_204 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  T_IsBaseType_152 ->
  T_IsBaseType_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseType'45'irrelevant_204 = erased
-- Once.Functor.Translate.WellFormedF-irrelevant
d_WellFormedF'45'irrelevant_228 ::
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  T_WellFormedF_178 ->
  T_WellFormedF_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedF'45'irrelevant_228 = erased
-- Once.Functor.Translate.wf-NatF
d_wf'45'NatF_250 :: T_WellFormedF_178
d_wf'45'NatF_250
  = coe
      C_wf'45'Sum_190 (coe C_wf'45'K_182 (coe C_base'45'Unit_154))
      (coe C_wf'45'Id_184)
