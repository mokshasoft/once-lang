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

module MAlonzo.Code.Once.Internal.FunctorMeaning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.FunctorMeaning.⟦_,_⟧-base
d_'10214'_'44'_'10215''45'base_8 ::
  Integer -> () -> () -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'44'_'10215''45'base_8 = erased
-- Once.Internal.FunctorMeaning.translateF
d_translateF_60 ::
  Integer ->
  () ->
  () ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6
d_translateF_60 ~v0 ~v1 ~v2 v3 = du_translateF_60 v3
du_translateF_60 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6
du_translateF_60 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> coe MAlonzo.Code.Once.Spec.Polynomial.C_SK_8
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12
             (coe du_translateF_60 (coe v1)) (coe du_translateF_60 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14
             (coe du_translateF_60 (coe v1)) (coe du_translateF_60 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.FunctorMeaning.μ-sem
d_μ'45'sem_90 ::
  Integer -> () -> () -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_μ'45'sem_90 = erased
-- Once.Internal.FunctorMeaning.ν-sem
d_ν'45'sem_100 ::
  Integer -> () -> () -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_ν'45'sem_100 = erased
-- Once.Internal.FunctorMeaning.⟦_,_⟧F-base
d_'10214'_'44'_'10215'F'45'base_110 ::
  Integer ->
  () -> () -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'44'_'10215'F'45'base_110 = erased
