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

module MAlonzo.Code.Once.Type.Honest where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Type.Honest.NotEmpty
d_NotEmpty_6 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_NotEmpty_6 = erased
-- Once.Type.Honest.NotSingleton
d_NotSingleton_16 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_NotSingleton_16 = erased
-- Once.Type.Honest.DataCod
d_DataCod_26 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_DataCod_26 = erased
-- Once.Type.Honest.Effectful
d_Effectful_34 :: MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> ()
d_Effectful_34 = erased
-- Once.Type.Honest.HonestCod
d_HonestCod_36 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_HonestCod_36 = erased
-- Once.Type.Honest.HonestFFI
d_HonestFFI_66 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_HonestFFI_66 = erased
-- Once.Type.Honest.isEff?
d_isEff'63'_102 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEff'63'_102 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.effectful?
d_effectful'63'_106 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> Maybe AgdaAny
d_effectful'63'_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.both
d_both_112 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_112 ~v0 ~v1 v2 v3 = du_both_112 v2 v3
du_both_112 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_112 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.either
d_either_122 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_either_122 ~v0 ~v1 v2 v3 = du_either_122 v2 v3
du_either_122 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_either_122 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v2))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notEmpty?
d_notEmpty'63'_130 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_notEmpty'63'_130 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             du_both_112 (coe d_notEmpty'63'_130 (coe v1))
             (coe d_notEmpty'63'_130 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             du_either_122 (coe d_notEmpty'63'_130 (coe v1))
             (coe d_notEmpty'63'_130 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notSingleton?
d_notSingleton'63'_142 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_notSingleton'63'_142 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             du_either_122 (coe d_notSingleton'63'_142 (coe v1))
             (coe d_notSingleton'63'_142 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             du_either_122
             (coe
                du_both_112 (coe d_notEmpty'63'_130 (coe v1))
                (coe d_notEmpty'63'_130 (coe v2)))
             (coe
                du_both_112 (coe d_notSingleton'63'_142 (coe v1))
                (coe d_notSingleton'63'_142 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.dataCod?
d_dataCod'63'_156 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_dataCod'63'_156 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe d_notEmpty'63'_130 (coe v1)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    du_both_112 (coe d_notEmpty'63'_130 (coe v1))
                    (coe d_notSingleton'63'_142 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             du_both_112 (coe d_notEmpty'63'_130 (coe v1))
             (coe d_notSingleton'63'_142 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honestCod?
d_honestCod'63'_168 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_honestCod'63'_168 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe d_effectful'63'_106 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe d_effectful'63'_106 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe d_dataCod'63'_156 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe d_dataCod'63'_156 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honest?
d_honest'63'_200 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_honest'63'_200 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe d_notEmpty'63'_130 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe d_notEmpty'63'_130 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe d_honestCod'63'_168 (coe v5) (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe d_honestCod'63'_168 (coe v5) (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
