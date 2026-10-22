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

module MAlonzo.Code.Once.Internal.Type.Honest where

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

-- Once.Internal.Type.Honest.NotEmpty
d_NotEmpty_8 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_NotEmpty_8 = erased
-- Once.Internal.Type.Honest.NotSingleton
d_NotSingleton_18 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_NotSingleton_18 = erased
-- Once.Internal.Type.Honest.DataCod
d_DataCod_28 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_DataCod_28 = erased
-- Once.Internal.Type.Honest.Effectful
d_Effectful_36 :: MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> ()
d_Effectful_36 = erased
-- Once.Internal.Type.Honest.HonestCod
d_HonestCod_38 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_HonestCod_38 = erased
-- Once.Internal.Type.Honest.HonestFFI
d_HonestFFI_68 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_HonestFFI_68 = erased
-- Once.Internal.Type.Honest.isEff?
d_isEff'63'_104 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEff'63'_104 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Honest.effectful?
d_effectful'63'_108 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> Maybe AgdaAny
d_effectful'63'_108 v0
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
-- Once.Internal.Type.Honest.both
d_both_114 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_114 ~v0 ~v1 v2 v3 = du_both_114 v2 v3
du_both_114 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_114 v0 v1
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
-- Once.Internal.Type.Honest.either
d_either_124 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_either_124 ~v0 ~v1 v2 v3 = du_either_124 v2 v3
du_either_124 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_either_124 v0 v1
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
-- Once.Internal.Type.Honest.notEmpty?
d_notEmpty'63'_132 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_notEmpty'63'_132 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             du_both_114 (coe d_notEmpty'63'_132 (coe v1))
             (coe d_notEmpty'63'_132 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             du_either_124 (coe d_notEmpty'63'_132 (coe v1))
             (coe d_notEmpty'63'_132 (coe v2))
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
-- Once.Internal.Type.Honest.notSingleton?
d_notSingleton'63'_144 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_notSingleton'63'_144 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             du_either_124 (coe d_notSingleton'63'_144 (coe v1))
             (coe d_notSingleton'63'_144 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             du_either_124
             (coe
                du_both_114 (coe d_notEmpty'63'_132 (coe v1))
                (coe d_notEmpty'63'_132 (coe v2)))
             (coe
                du_both_114 (coe d_notSingleton'63'_144 (coe v1))
                (coe d_notSingleton'63'_144 (coe v2)))
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
-- Once.Internal.Type.Honest.dataCod?
d_dataCod'63'_158 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_dataCod'63'_158 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe d_notEmpty'63'_132 (coe v1)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    du_both_114 (coe d_notEmpty'63'_132 (coe v1))
                    (coe d_notSingleton'63'_144 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             du_both_114 (coe d_notEmpty'63'_132 (coe v1))
             (coe d_notSingleton'63'_144 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Honest.honestCod?
d_honestCod'63'_170 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_honestCod'63'_170 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe d_effectful'63'_108 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe d_effectful'63'_108 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe d_dataCod'63'_158 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe d_dataCod'63'_158 (coe v0) (coe v1)
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
-- Once.Internal.Type.Honest.honest?
d_honest'63'_202 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Maybe AgdaAny
d_honest'63'_202 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe d_notEmpty'63'_132 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe d_notEmpty'63'_132 (coe v0)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe d_honestCod'63'_170 (coe v5) (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe d_honestCod'63'_170 (coe v5) (coe v3)
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
