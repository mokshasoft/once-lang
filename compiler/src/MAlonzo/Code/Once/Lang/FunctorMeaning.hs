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

module MAlonzo.Code.Once.Lang.FunctorMeaning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Type

-- Once.Lang.FunctorMeaning.⟦_,_⟧-base
d_'10214'_'44'_'10215''45'base_6 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'44'_'10215''45'base_6 = erased
-- Once.Lang.FunctorMeaning.translateF
d_translateF_56 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_translateF_56 ~v0 ~v1 v2 = du_translateF_56 v2
du_translateF_56 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_translateF_56 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v1
        -> coe MAlonzo.Code.Once.Lang.Polynomial.C_SK_8
      MAlonzo.Code.Once.Lang.Type.C_Id_14
        -> coe MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14
             (coe du_translateF_56 (coe v1)) (coe du_translateF_56 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.FunctorMeaning.μ-sem
d_μ'45'sem_84 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_μ'45'sem_84 = erased
-- Once.Lang.FunctorMeaning.ν-sem
d_ν'45'sem_92 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_ν'45'sem_92 = erased
-- Once.Lang.FunctorMeaning.⟦_,_⟧F-base
d_'10214'_'44'_'10215'F'45'base_100 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'44'_'10215'F'45'base_100 = erased
