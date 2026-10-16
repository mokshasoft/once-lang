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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Honest

-- Once.Type.Honest.both-c
d_both'45'c_20 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both'45'c_20 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_both'45'c_20 v4 v5
du_both'45'c_20 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both'45'c_20 v0 v1
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
d_either'45'l_38 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_either'45'l_38 ~v0 ~v1 ~v2 ~v3 v4 = du_either'45'l_38 v4
du_either'45'l_38 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_either'45'l_38 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.either-r
d_either'45'r_54 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_either'45'r_54 ~v0 ~v1 v2 ~v3 v4 = du_either'45'r_54 v2 v4
du_either'45'r_54 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_either'45'r_54 v0 v1
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
d_notEmpty'63''45'complete_64 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_notEmpty'63''45'complete_64 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_both'45'c_20
                    (coe d_notEmpty'63''45'complete_64 (coe v2) (coe v4))
                    (coe d_notEmpty'63''45'complete_64 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_either'45'l_38
                    (coe d_notEmpty'63''45'complete_64 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_either'45'r_54
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Honest.d_notEmpty'63'_126 (coe v2))
                    (coe d_notEmpty'63''45'complete_64 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.notSingleton?-complete
d_notSingleton'63''45'complete_90 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_notSingleton'63''45'complete_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_either'45'l_38
                    (coe d_notSingleton'63''45'complete_90 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_either'45'r_54
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Honest.d_notSingleton'63'_138 (coe v2))
                    (coe d_notSingleton'63''45'complete_90 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_either'45'l_38
                           (coe
                              du_both'45'c_20
                              (coe d_notEmpty'63''45'complete_64 (coe v2) (coe v5))
                              (coe d_notEmpty'63''45'complete_64 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_either'45'r_54
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Honest.du_both_108
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Honest.d_notEmpty'63'_126 (coe v2))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Honest.d_notEmpty'63'_126 (coe v3)))
                           (coe
                              du_both'45'c_20
                              (coe d_notSingleton'63''45'complete_90 (coe v2) (coe v5))
                              (coe d_notSingleton'63''45'complete_90 (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.dataCod?-complete
d_dataCod'63''45'complete_126 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dataCod'63''45'complete_126 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe d_notEmpty'63''45'complete_64 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_both'45'c_20
                    (coe d_notEmpty'63''45'complete_64 (coe v1) (coe v3))
                    (coe d_notSingleton'63''45'complete_90 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_both'45'c_20
                    (coe d_notEmpty'63''45'complete_64 (coe v1) (coe v3))
                    (coe d_notSingleton'63''45'complete_90 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_both'45'c_20
                    (coe d_notEmpty'63''45'complete_64 (coe v1) (coe v3))
                    (coe d_notSingleton'63''45'complete_90 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.effectful?-complete
d_effectful'63''45'complete_154 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_effectful'63''45'complete_154 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased))
-- Once.Type.Honest.honestCod?-complete
d_honestCod'63''45'complete_162 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honestCod'63''45'complete_162 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe d_effectful'63''45'complete_154 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe d_effectful'63''45'complete_154 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v3 v4
        -> coe d_dataCod'63''45'complete_126 (coe v0) (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v3 v4
        -> coe d_dataCod'63''45'complete_126 (coe v0) (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v6 v7
               -> coe d_honestCod'63''45'complete_162 (coe v7) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honest?-complete
d_honest'63''45'complete_214 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honest'63''45'complete_214 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
        -> coe d_notEmpty'63''45'complete_64 (coe v0) (coe v1)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
        -> coe d_notEmpty'63''45'complete_64 (coe v0) (coe v1)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v5 v6
               -> coe d_honestCod'63''45'complete_162 (coe v6) (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
