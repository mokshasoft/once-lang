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

module MAlonzo.Code.Once.Internal.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Value.⟦μ⟧
d_'10214'μ'10215'_12 ::
  () -> () -> Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_12 = erased
-- Once.Internal.Value.⟦ν⟧
d_'10214'ν'10215'_16 ::
  () -> () -> Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_16 = erased
-- Once.Internal.Value.⟦_⟧
d_'10214'_'10215'_20 ::
  () -> () -> Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_20 = erased
-- Once.Internal.Value.⟦_⟧ᵍ
d_'10214'_'10215''7501'_54 ::
  () -> () -> Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_54 = erased
-- Once.Internal.Value.eraseᵍ
d_erase'7501'_110 ::
  () ->
  () ->
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_110 ~v0 ~v1 ~v2 v3 v4 = du_erase'7501'_110 v3 v4
du_erase'7501'_110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
du_erase'7501'_110 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_erase'7501'_110 (coe v2) (coe v4))
                    (coe du_erase'7501'_110 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_erase'7501'_110 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_erase'7501'_110 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                -> coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Once.Res.C_returns_12
                                          (coe du_erase'7501'_110 (coe v4) (coe v1 v8)))
                              MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                -> coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Once.Res.du_mapRes_22
                                          (coe du_erase'7501'_110 (coe v4)) (coe v1 v8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_eff_44
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Res.du_mapRes_22
                                   (coe du_erase'7501'_110 (coe v4)) (coe v1 v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.⟦_⟧F
d_'10214'_'10215'F_226 ::
  () ->
  () -> Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_226 = erased
-- Once.Internal.Value.coerce-functor
d_coerce'45'functor_252 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_252 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_coerce'45'functor_252 v3 v5
du_coerce'45'functor_252 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> AgdaAny
du_coerce'45'functor_252 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_252 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_252 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_252 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_252 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_296 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_296 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_coerce'45'functor'8315''185'_296 v3 v5
du_coerce'45'functor'8315''185'_296 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_296 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_296 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_296 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_296 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_296 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.sem-fmap
d_sem'45'fmap_342 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_342 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_sem'45'fmap_342 v3 v6 v7
du_sem'45'fmap_342 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_342 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v3 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1 v2
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_342 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_342 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_342 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_342 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.coerce-full-to-base
d_coerce'45'full'45'to'45'base_384 ::
  () ->
  () ->
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_384 ~v0 ~v1 ~v2 v3 v4
  = du_coerce'45'full'45'to'45'base_384 v3 v4
du_coerce'45'full'45'to'45'base_384 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_384 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_384 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_384 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_384 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_384 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.coerce-base-to-full
d_coerce'45'base'45'to'45'full_420 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_420 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_coerce'45'base'45'to'45'full_420 v4 v5 v6
du_coerce'45'base'45'to'45'full_420 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_420 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_420 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_420 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_420 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_420 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.coerce-μ-in
d_coerce'45'μ'45'in_454 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_454 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_coerce'45'μ'45'in_454 v3 v5
du_coerce'45'μ'45'in_454 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_454 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe du_coerce'45'full'45'to'45'base_384 (coe v2) (coe v1)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_454 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_454 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_454 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_454 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.coerce-μ-out
d_coerce'45'μ'45'out_500 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_500 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_coerce'45'μ'45'out_500 v4 v5 v7
du_coerce'45'μ'45'out_500 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_500 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_wf'45'K_126 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_38 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_420 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_wf'45'Id_128 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_wf'45''8853'_134 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_500 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_500 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_wf'45''8855'_140 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_500 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_500 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.sem-In
d_sem'45'In_542 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_542 ~v0 ~v1 ~v2 v3 v4 = du_sem'45'In_542 v3 v4
du_sem'45'In_542 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
du_sem'45'In_542 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86
      (coe du_coerce'45'μ'45'in_454 (coe v0) (coe v1))
-- Once.Internal.Value.sem-Out
d_sem'45'Out_554 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_554 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_sem'45'Out_554 v4 v5 v6
du_sem'45'Out_554 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'Out_554 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_500 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Internal.Polynomial.d_outS_8 (coe v2))
-- Once.Internal.Value.sem-cata
d_sem'45'cata_570 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_570 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_sem'45'cata_570 v4 v5 v7
du_sem'45'cata_570 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'cata_570 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Polynomial.du_cataS_30
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_60
         (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_500 (coe v0) (coe v1) (coe v3))))
-- Once.Internal.Value.sem-para
d_sem'45'para_590 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_590 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_sem'45'para_590 v4 v5 v7 v8
du_sem'45'para_590 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'para_590 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_570 v0 v1 (coe du_alg''_606 (coe v0) (coe v2)) v3)
-- Once.Internal.Value._.alg'
d_alg''_606 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_606 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 v9
  = du_alg''_606 v4 v7 v9
du_alg''_606 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_606 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_542 (coe v0)
         (coe
            du_sem'45'fmap_342 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Internal.Value.coerce-ν-in
d_coerce'45'ν'45'in_616 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_616 ~v0 ~v1 ~v2 = du_coerce'45'ν'45'in_616
du_coerce'45'ν'45'in_616 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_616 v0 v1 v2
  = coe du_coerce'45'μ'45'in_454 v0 v2
-- Once.Internal.Value.coerce-ν-out
d_coerce'45'ν'45'out_626 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_626 ~v0 ~v1 ~v2 ~v3 v4
  = du_coerce'45'ν'45'out_626 v4
du_coerce'45'ν'45'out_626 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_626 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_500 (coe v0) v1 v3
-- Once.Internal.Value.sem-CoOut
d_sem'45'CoOut_634 ::
  () ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_16 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_634 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_sem'45'CoOut_634 v4 v5 v6
du_sem'45'CoOut_634 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_16 ->
  MAlonzo.Code.Once.Res.T_Res_6
du_sem'45'CoOut_634 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Res.du_mapRes_22
      (coe du_coerce'45'ν'45'out_626 v0 v1 erased)
      (coe MAlonzo.Code.Once.Internal.Polynomial.d_unfoldS_22 (coe v2))
-- Once.Internal.Value.sem-CoIn
d_sem'45'CoIn_646 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'CoIn_646 ~v0 ~v1 ~v2 v3 v4 = du_sem'45'CoIn_646 v3 v4
du_sem'45'CoIn_646 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
du_sem'45'CoIn_646 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Polynomial.C_constructor_24
      (coe
         MAlonzo.Code.Once.Res.C_returns_12
         (coe du_coerce'45'ν'45'in_616 v0 erased v1))
-- Once.Internal.Value.sem-ana
d_sem'45'ana_658 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'ana_658 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sem'45'ana_658 v2 v3 v5 v6
du_sem'45'ana_658 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
du_sem'45'ana_658 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Polynomial.C_constructor_24
      (coe du_semAnaLayer_666 (coe v0) (coe v1) (coe v2) (coe v2 v3))
-- Once.Internal.Value.semAnaLayer
d_semAnaLayer_666 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_666 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_semAnaLayer_666 v2 v3 v5 v6
du_semAnaLayer_666 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_semAnaLayer_666 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v3
      MAlonzo.Code.Once.Res.C_returns_12 v4
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe
                du_sfmapSemAna_676 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_60
                   (coe v1))
                (coe v2) (coe du_coerce'45'ν'45'in_616 v1 erased v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Value.sfmapSemAna
d_sfmapSemAna_676 ::
  () ->
  () ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_676 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7
  = du_sfmapSemAna_676 v2 v3 v4 v6 v7
du_sfmapSemAna_676 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
du_sfmapSemAna_676 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v4
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_sem'45'ana_658 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       du_sfmapSemAna_676 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       du_sfmapSemAna_676 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sfmapSemAna_676 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe
                       du_sfmapSemAna_676 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
