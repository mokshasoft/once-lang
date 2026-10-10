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
import qualified MAlonzo.Code.Once.Type

-- Once.Type.Honest.NotEmpty
d_NotEmpty_6 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_NotEmpty_6 = erased
-- Once.Type.Honest.NotSingleton
d_NotSingleton_16 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_NotSingleton_16 = erased
-- Once.Type.Honest.DataCod
d_DataCod_26 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_DataCod_26 = erased
-- Once.Type.Honest.HonestCod
d_HonestCod_32 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_HonestCod_32 = erased
-- Once.Type.Honest.HonestFFI
d_HonestFFI_70 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_HonestFFI_70 = erased
-- Once.Type.Honest.isEff?
d_isEff'63'_90 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEff'63'_90 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.both
d_both_96 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_96 ~v0 ~v1 v2 v3 = du_both_96 v2 v3
du_both_96 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_96 v0 v1
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
d_either_106 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_either_106 ~v0 ~v1 v2 v3 = du_either_106 v2 v3
du_either_106 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_either_106 v0 v1
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
d_notEmpty'63'_114 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_notEmpty'63'_114 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             du_both_96 (coe d_notEmpty'63'_114 (coe v1))
             (coe d_notEmpty'63'_114 (coe v2))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             du_either_106 (coe d_notEmpty'63'_114 (coe v1))
             (coe d_notEmpty'63'_114 (coe v2))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notSingleton?
d_notSingleton'63'_126 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_notSingleton'63'_126 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             du_either_106 (coe d_notSingleton'63'_126 (coe v1))
             (coe d_notSingleton'63'_126 (coe v2))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             du_either_106
             (coe
                du_both_96 (coe d_notEmpty'63'_114 (coe v1))
                (coe d_notEmpty'63'_114 (coe v2)))
             (coe
                du_both_96 (coe d_notSingleton'63'_126 (coe v1))
                (coe d_notSingleton'63'_126 (coe v2)))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.dataCod?
d_dataCod'63'_140 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_dataCod'63'_140 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34 -> coe d_notEmpty'63'_114 (coe v1)
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             du_both_96 (coe d_notEmpty'63'_114 (coe v1))
             (coe d_notSingleton'63'_126 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honestCod?
d_honestCod'63'_150 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_honestCod'63'_150 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe d_isEff'63'_90 (coe v0)
      MAlonzo.Code.Once.Type.C_Void_122 -> coe d_isEff'63'_90 (coe v0)
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe d_dataCod'63'_140 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe d_dataCod'63'_140 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe d_honestCod'63'_150 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honest?
d_honest'63'_190 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_honest'63'_190 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe d_notEmpty'63'_114 (coe v0)
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe d_notEmpty'63'_114 (coe v0)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> coe d_honestCod'63'_150 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.both-c
d_both'45'c_222 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both'45'c_222 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_both'45'c_222 v4 v5
du_both'45'c_222 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both'45'c_222 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.either-l
d_either'45'l_240 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_either'45'l_240 ~v0 ~v1 ~v2 ~v3 v4 = du_either'45'l_240 v4
du_either'45'l_240 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_either'45'l_240 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.either-r
d_either'45'r_256 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_either'45'r_256 ~v0 ~v1 v2 ~v3 v4 = du_either'45'r_256 v2 v4
du_either'45'r_256 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_either'45'r_256 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)) erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v2)) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notEmpty?-complete
d_notEmpty'63''45'complete_266 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_notEmpty'63''45'complete_266 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_both'45'c_222
                    (coe d_notEmpty'63''45'complete_266 (coe v2) (coe v4))
                    (coe d_notEmpty'63''45'complete_266 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_either'45'l_240
                    (coe d_notEmpty'63''45'complete_266 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_either'45'r_256 (coe d_notEmpty'63'_114 (coe v2))
                    (coe d_notEmpty'63''45'complete_266 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notSingleton?-complete
d_notSingleton'63''45'complete_292 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_notSingleton'63''45'complete_292 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_either'45'l_240
                    (coe d_notSingleton'63''45'complete_292 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_either'45'r_256 (coe d_notSingleton'63'_126 (coe v2))
                    (coe d_notSingleton'63''45'complete_292 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_either'45'l_240
                           (coe
                              du_both'45'c_222
                              (coe d_notEmpty'63''45'complete_266 (coe v2) (coe v5))
                              (coe d_notEmpty'63''45'complete_266 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_either'45'r_256
                           (coe
                              du_both_96 (coe d_notEmpty'63'_114 (coe v2))
                              (coe d_notEmpty'63'_114 (coe v3)))
                           (coe
                              du_both'45'c_222
                              (coe d_notSingleton'63''45'complete_292 (coe v2) (coe v5))
                              (coe d_notSingleton'63''45'complete_292 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.dataCod?-complete
d_dataCod'63''45'complete_328 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dataCod'63''45'complete_328 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe d_notEmpty'63''45'complete_266 (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C_eff_36
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_both'45'c_222
                    (coe d_notEmpty'63''45'complete_266 (coe v1) (coe v3))
                    (coe d_notSingleton'63''45'complete_292 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honestCod?-complete
d_honestCod'63''45'complete_346 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honestCod'63''45'complete_346 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe d_dataCod'63''45'complete_328 (coe v0) (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe d_dataCod'63''45'complete_328 (coe v0) (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> coe d_honestCod'63''45'complete_346 (coe v7) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honest?-complete
d_honest'63''45'complete_394 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honest'63''45'complete_394 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe d_notEmpty'63''45'complete_266 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe d_notEmpty'63''45'complete_266 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe d_honestCod'63''45'complete_346 (coe v6) (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
