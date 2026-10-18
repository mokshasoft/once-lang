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

module MAlonzo.Code.Once.Lang.Type.Honest where

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
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade

-- Once.Lang.Type.Honest.NotEmpty
d_NotEmpty_8 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_NotEmpty_8 = erased
-- Once.Lang.Type.Honest.NotSingleton
d_NotSingleton_18 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_NotSingleton_18 = erased
-- Once.Lang.Type.Honest.DataCod
d_DataCod_28 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_DataCod_28 = erased
-- Once.Lang.Type.Honest.Effectful
d_Effectful_36 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> ()
d_Effectful_36 = erased
-- Once.Lang.Type.Honest.HonestCod
d_HonestCod_38 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_HonestCod_38 = erased
-- Once.Lang.Type.Honest.HonestFFI
d_HonestFFI_76 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_HonestFFI_76 = erased
-- Once.Lang.Type.Honest.isEff?
d_isEff'63'_96 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEff'63'_96 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.effectful?
d_effectful'63'_100 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> Maybe AgdaAny
d_effectful'63'_100 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.both
d_both_106 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_106 ~v0 ~v1 v2 v3 = du_both_106 v2 v3
du_both_106 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_106 v0 v1
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
-- Once.Lang.Type.Honest.either
d_either_116 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_either_116 ~v0 ~v1 v2 v3 = du_either_116 v2 v3
du_either_116 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_either_116 v0 v1
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
-- Once.Lang.Type.Honest.notEmpty?
d_notEmpty'63'_124 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe AgdaAny
d_notEmpty'63'_124 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             du_both_106 (coe d_notEmpty'63'_124 (coe v1))
             (coe d_notEmpty'63'_124 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             du_either_116 (coe d_notEmpty'63'_124 (coe v1))
             (coe d_notEmpty'63'_124 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.notSingleton?
d_notSingleton'63'_136 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe AgdaAny
d_notSingleton'63'_136 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             du_either_116 (coe d_notSingleton'63'_136 (coe v1))
             (coe d_notSingleton'63'_136 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             du_either_116
             (coe
                du_both_106 (coe d_notEmpty'63'_124 (coe v1))
                (coe d_notEmpty'63'_124 (coe v2)))
             (coe
                du_both_106 (coe d_notSingleton'63'_136 (coe v1))
                (coe d_notSingleton'63'_136 (coe v2)))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.dataCod?
d_dataCod'63'_150 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe AgdaAny
d_dataCod'63'_150 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe d_notEmpty'63'_124 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             du_both_106 (coe d_notEmpty'63'_124 (coe v1))
             (coe d_notSingleton'63'_136 (coe v1))
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             du_both_106 (coe d_notEmpty'63'_124 (coe v1))
             (coe d_notSingleton'63'_136 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.honestCod?
d_honestCod'63'_162 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe AgdaAny
d_honestCod'63'_162 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe d_effectful'63'_100 (coe v0)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe d_effectful'63'_100 (coe v0)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> coe d_dataCod'63'_150 (coe v0) (coe v1)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> coe d_dataCod'63'_150 (coe v0) (coe v1)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v5 v6
               -> coe d_honestCod'63'_162 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Honest.honest?
d_honest'63'_202 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe AgdaAny
d_honest'63'_202 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe d_notEmpty'63'_124 (coe v0)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe d_notEmpty'63'_124 (coe v0)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe d_honestCod'63'_162 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
