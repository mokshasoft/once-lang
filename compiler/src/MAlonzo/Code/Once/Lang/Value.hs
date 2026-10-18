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

module MAlonzo.Code.Once.Lang.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed

-- Once.Lang.Value.⟦μ⟧
d_'10214'μ'10215'_10 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_10 = erased
-- Once.Lang.Value.⟦ν⟧
d_'10214'ν'10215'_12 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_12 = erased
-- Once.Lang.Value.⟦_⟧
d_'10214'_'10215'_14 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_14 = erased
-- Once.Lang.Value.⟦_⟧ᵍ
d_'10214'_'10215''7501'_46 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_46 = erased
-- Once.Lang.Value.eraseᵍ
d_erase'7501'_104 ::
  () ->
  () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_104 ~v0 ~v1 v2 v3 = du_erase'7501'_104 v2 v3
du_erase'7501'_104 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_erase'7501'_104 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_erase'7501'_104 (coe v2) (coe v4))
                    (coe du_erase'7501'_104 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_erase'7501'_104 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_erase'7501'_104 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Res.C_returns_14
                                   (coe du_erase'7501'_104 (coe v4) (coe v1 v7)))
                       MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Res.du_mapRes_24
                                   (coe du_erase'7501'_104 (coe v4)) (coe v1 v7))
                       MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Res.du_mapRes_24
                                   (coe du_erase'7501'_104 (coe v4)) (coe v1 v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.⟦_⟧F
d_'10214'_'10215'F_222 ::
  () -> () -> MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_222 = erased
-- Once.Lang.Value.coerce-functor
d_coerce'45'functor_246 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_246 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor_246 v2 v4
du_coerce'45'functor_246 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_coerce'45'functor_246 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_246 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_246 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_246 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_246 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_288 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_288 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor'8315''185'_288 v2 v4
du_coerce'45'functor'8315''185'_288 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_288 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_288 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_288 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_288 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_288 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.sem-fmap
d_sem'45'fmap_332 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_332 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap_332 v2 v5 v6
du_sem'45'fmap_332 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_332 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v3 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1 v2
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_332 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_332 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_332 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_332 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.coerce-full-to-base
d_coerce'45'full'45'to'45'base_372 ::
  () ->
  () -> MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_372 ~v0 ~v1 v2 v3
  = du_coerce'45'full'45'to'45'base_372 v2 v3
du_coerce'45'full'45'to'45'base_372 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_372 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_372 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_372 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_372 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_372 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.coerce-base-to-full
d_coerce'45'base'45'to'45'full_404 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_404 ~v0 ~v1 v2 v3 v4
  = du_coerce'45'base'45'to'45'full_404 v2 v3 v4
du_coerce'45'base'45'to'45'full_404 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_404 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_404 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_404 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_404 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_404 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.coerce-μ-in
d_coerce'45'μ'45'in_436 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_436 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'μ'45'in_436 v2 v4
du_coerce'45'μ'45'in_436 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_436 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v2
        -> coe du_coerce'45'full'45'to'45'base_372 (coe v2) (coe v1)
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_436 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_436 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_436 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_436 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.coerce-μ-out
d_coerce'45'μ'45'out_478 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_478 ~v0 ~v1 v2 v3 ~v4 v5
  = du_coerce'45'μ'45'out_478 v2 v3 v5
du_coerce'45'μ'45'out_478 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_478 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_404 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_478 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_478 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_478 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_478 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.sem-In
d_sem'45'In_518 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_518 ~v0 ~v1 v2 v3 = du_sem'45'In_518 v2 v3
du_sem'45'In_518 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
du_sem'45'In_518 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Polynomial.C_'10216'_'10217'_86
      (coe du_coerce'45'μ'45'in_436 (coe v0) (coe v1))
-- Once.Lang.Value.sem-Out
d_sem'45'Out_526 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_526 ~v0 ~v1 v2 v3 v4 = du_sem'45'Out_526 v2 v3 v4
du_sem'45'Out_526 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'Out_526 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_478 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Lang.Polynomial.d_outS_90 (coe v2))
-- Once.Lang.Value.sem-cata
d_sem'45'cata_538 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_538 ~v0 ~v1 v2 v3 ~v4 v5
  = du_sem'45'cata_538 v2 v3 v5
du_sem'45'cata_538 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'cata_538 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Polynomial.du_cataS_112
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_478 (coe v0) (coe v1) (coe v3))))
-- Once.Lang.Value.sem-para
d_sem'45'para_554 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_554 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sem'45'para_554 v2 v3 v5 v6
du_sem'45'para_554 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_sem'45'para_554 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_538 v0 v1 (coe du_alg''_570 (coe v0) (coe v2)) v3)
-- Once.Lang.Value._.alg'
d_alg''_570 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_570 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 = du_alg''_570 v2 v5 v7
du_alg''_570 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_570 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_518 (coe v0)
         (coe
            du_sem'45'fmap_332 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Lang.Value.coerce-ν-in
d_coerce'45'ν'45'in_578 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_578 ~v0 ~v1 = du_coerce'45'ν'45'in_578
du_coerce'45'ν'45'in_578 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_578 v0 v1 v2
  = coe du_coerce'45'μ'45'in_436 v0 v2
-- Once.Lang.Value.coerce-ν-out
d_coerce'45'ν'45'out_584 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_584 ~v0 ~v1 v2 = du_coerce'45'ν'45'out_584 v2
du_coerce'45'ν'45'out_584 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_584 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_478 (coe v0) v1 v3
-- Once.Lang.Value.sem-CoOut
d_sem'45'CoOut_588 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_588 ~v0 ~v1 v2 v3 v4 = du_sem'45'CoOut_588 v2 v3 v4
du_sem'45'CoOut_588 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_sem'45'CoOut_588 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Res.du_mapRes_24
      (coe du_coerce'45'ν'45'out_584 v0 v1 erased)
      (coe MAlonzo.Code.Once.Lang.Polynomial.d_unfoldS_104 (coe v2))
-- Once.Lang.Value.sem-CoIn
d_sem'45'CoIn_598 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_598 ~v0 ~v1 v2 v3 = du_sem'45'CoIn_598 v2 v3
du_sem'45'CoIn_598 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
du_sem'45'CoIn_598 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Polynomial.C_constructor_106
      (coe
         MAlonzo.Code.Once.Lang.Res.C_returns_14
         (coe du_coerce'45'ν'45'in_578 v0 erased v1))
-- Once.Lang.Value.sem-ana
d_sem'45'ana_608 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_608 ~v0 ~v1 v2 ~v3 v4 v5 = du_sem'45'ana_608 v2 v4 v5
du_sem'45'ana_608 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
du_sem'45'ana_608 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Polynomial.C_constructor_106
      (coe du_semAnaLayer_614 (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.Value.semAnaLayer
d_semAnaLayer_614 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_614 ~v0 ~v1 v2 ~v3 v4 v5
  = du_semAnaLayer_614 v2 v4 v5
du_semAnaLayer_614 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
du_semAnaLayer_614 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Res.C_stopped_12 -> coe v2
      MAlonzo.Code.Once.Lang.Res.C_returns_14 v3
        -> coe
             MAlonzo.Code.Once.Lang.Res.C_returns_14
             (coe
                du_sfmapSemAna_622 (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
                (coe v1) (coe du_coerce'45'ν'45'in_578 v0 erased v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Value.sfmapSemAna
d_sfmapSemAna_622 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_622 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sfmapSemAna_622 v2 v3 v5 v6
du_sfmapSemAna_622 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
du_sfmapSemAna_622 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_sem'45'ana_608 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapSemAna_622 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapSemAna_622 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapSemAna_622 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapSemAna_622 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
