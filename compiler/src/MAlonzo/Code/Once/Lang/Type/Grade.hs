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

module MAlonzo.Code.Once.Lang.Type.Grade where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- Once.Lang.Type.Grade.Quantity
d_Quantity_8 = ()
data T_Quantity_8 = C_Zero_10 | C_One_12 | C_Many_14
-- Once.Lang.Type.Grade._+q_
d__'43'q__16 :: T_Quantity_8 -> T_Quantity_8 -> T_Quantity_8
d__'43'q__16 v0 v1
  = case coe v0 of
      C_Zero_10 -> coe v1
      C_One_12
        -> case coe v1 of
             C_Zero_10 -> coe v0
             C_One_12 -> coe C_Many_14
             C_Many_14 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_14 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade._*q_
d__'42'q__20 :: T_Quantity_8 -> T_Quantity_8 -> T_Quantity_8
d__'42'q__20 v0 v1
  = case coe v0 of
      C_Zero_10 -> coe v0
      C_One_12 -> coe v1
      C_Many_14
        -> case coe v1 of
             C_Zero_10 -> coe v1
             C_One_12 -> coe v0
             C_Many_14 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade._⊔q_
d__'8852'q__22 :: T_Quantity_8 -> T_Quantity_8 -> T_Quantity_8
d__'8852'q__22 v0 v1
  = case coe v0 of
      C_Zero_10 -> coe v1
      C_One_12
        -> case coe v1 of
             C_Zero_10 -> coe v0
             C_One_12 -> coe v1
             C_Many_14 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_14 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade._≤q_
d__'8804'q__26 :: T_Quantity_8 -> T_Quantity_8 -> Bool
d__'8804'q__26 v0 v1
  = case coe v0 of
      C_Zero_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_One_12
        -> case coe v1 of
             C_Zero_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Many_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_14
        -> case coe v1 of
             C_Zero_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Many_14 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade.≤q-Many
d_'8804'q'45'Many_30 ::
  T_Quantity_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804'q'45'Many_30 = erased
-- Once.Lang.Type.Grade.Purity
d_Purity_32 = ()
data T_Purity_32 = C_pure_34 | C_act_36 | C_eff_38
-- Once.Lang.Type.Grade._⊔p_
d__'8852'p__40 :: T_Purity_32 -> T_Purity_32 -> T_Purity_32
d__'8852'p__40 v0 v1
  = case coe v0 of
      C_pure_34 -> coe v1
      C_act_36
        -> case coe v1 of
             C_pure_34 -> coe v0
             C_act_36 -> coe v1
             C_eff_38 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_38 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade._·p_
d__'183'p__44 :: T_Purity_32 -> T_Purity_32 -> T_Purity_32
d__'183'p__44 v0 v1
  = case coe v0 of
      C_pure_34 -> coe v1
      C_act_36
        -> case coe v1 of
             C_pure_34 -> coe v0
             C_act_36 -> coe v1
             C_eff_38 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_38 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade.EffGrade
d_EffGrade_48 a0 = ()
data T_EffGrade_48 = C_eg'45'act_50 | C_eg'45'eff_52
-- Once.Lang.Type.Grade.positionGrade
d_positionGrade_54 :: T_Quantity_8 -> T_Purity_32 -> T_Purity_32
d_positionGrade_54 v0 v1
  = case coe v0 of
      C_Zero_10 -> coe C_pure_34
      C_One_12 -> coe v1
      C_Many_14 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade.ArrowKind
d_ArrowKind_60 = ()
data T_ArrowKind_60 = C_mk'45'kind_70 T_Quantity_8 T_Purity_32
-- Once.Lang.Type.Grade.ArrowKind.quantity
d_quantity_66 :: T_ArrowKind_60 -> T_Quantity_8
d_quantity_66 v0
  = case coe v0 of
      C_mk'45'kind_70 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade.ArrowKind.purity
d_purity_68 :: T_ArrowKind_60 -> T_Purity_32
d_purity_68 v0
  = case coe v0 of
      C_mk'45'kind_70 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Type.Grade.pureK
d_pureK_72 :: T_Quantity_8 -> T_ArrowKind_60
d_pureK_72 v0 = coe C_mk'45'kind_70 (coe v0) (coe C_pure_34)
-- Once.Lang.Type.Grade.effK
d_effK_76 :: T_ArrowKind_60
d_effK_76 = coe C_mk'45'kind_70 (coe C_Many_14) (coe C_eff_38)
