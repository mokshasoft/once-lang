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
import qualified MAlonzo.Code.Once.Type

-- Once.Type.Honest.HonestCod
d_HonestCod_6 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_HonestCod_6 = erased
-- Once.Type.Honest.HonestFFI
d_HonestFFI_36 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_HonestFFI_36 = erased
-- Once.Type.Honest.isEff?
d_isEff'63'_48 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEff'63'_48 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Honest.honestCod?
d_honestCod'63'_54 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_honestCod'63'_54 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe d_isEff'63'_48 (coe v0)
      MAlonzo.Code.Once.Type.C_Void_122 -> coe d_isEff'63'_48 (coe v0)
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe d_honestCod'63'_54 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
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
d_honest'63'_86 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe AgdaAny
d_honest'63'_86 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> coe d_honestCod'63'_54 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
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
-- Once.Type.Honest.honestCod?-complete
d_honestCod'63''45'complete_102 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honestCod'63''45'complete_102 ~v0 v1 v2
  = du_honestCod'63''45'complete_102 v1 v2
du_honestCod'63''45'complete_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_honestCod'63''45'complete_102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> coe
             seq (coe v3)
             (coe du_honestCod'63''45'complete_102 (coe v4) (coe v1))
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
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
-- Once.Type.Honest.honest?-complete
d_honest'63''45'complete_138 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_honest'63''45'complete_138 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> coe
             seq (coe v3)
             (coe du_honestCod'63''45'complete_102 (coe v4) (coe v1))
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)
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
