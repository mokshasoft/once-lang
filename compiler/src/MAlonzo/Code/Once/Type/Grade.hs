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

module MAlonzo.Code.Once.Type.Grade where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Type.Grade._≤qᵇ_
d__'8804'q'7495'__6 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> Bool
d__'8804'q'7495'__6 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Grade.≤qᵇ→≤q
d_'8804'q'7495''8594''8804'q_12 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
d_'8804'q'7495''8594''8804'q_12 v0 v1 ~v2
  = du_'8804'q'7495''8594''8804'q_12 v0 v1
du_'8804'q'7495''8594''8804'q_12 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8804'q__22
du_'8804'q'7495''8594''8804'q_12 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Grade.≤q-Many
d_'8804'q'45'Many_18 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'Many_18 = erased
-- Once.Type.Grade._⊔q_
d__'8852'q__20 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
d__'8852'q__20 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe v0
             MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Grade._⊔p_
d__'8852'p__24 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40
d__'8852'p__24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
                      -> coe seq (coe v3) (coe v0)
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44 -> coe v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Grade.pureK
d_pureK_28 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80
d_pureK_28 v0
  = coe
      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_fin_42
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
-- Once.Type.Grade.effK
d_effK_32 :: MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80
d_effK_32
  = coe
      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
      (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44)
