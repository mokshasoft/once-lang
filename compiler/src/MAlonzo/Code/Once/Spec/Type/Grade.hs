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

module MAlonzo.Code.Once.Spec.Type.Grade where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool

-- Once.Spec.Type.Grade.Quantity
d_Quantity_8 = ()
data T_Quantity_8 = C_Zero_10 | C_One_12 | C_Many_14
-- Once.Spec.Type.Grade._+q_
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
-- Once.Spec.Type.Grade._*q_
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
-- Once.Spec.Type.Grade._⊔q_
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
-- Once.Spec.Type.Grade._≤q_
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
-- Once.Spec.Type.Grade.Purity
d_Purity_28 = ()
data T_Purity_28 = C_pure_30 | C_eff_32
-- Once.Spec.Type.Grade._⊔p_
d__'8852'p__34 :: T_Purity_28 -> T_Purity_28 -> T_Purity_28
d__'8852'p__34 v0 v1
  = case coe v0 of
      C_pure_30 -> coe v1
      C_eff_32 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Grade.ArrowKind
d_ArrowKind_38 = ()
data T_ArrowKind_38 = C_mk'45'kind_48 T_Quantity_8 T_Purity_28
-- Once.Spec.Type.Grade.ArrowKind.quantity
d_quantity_44 :: T_ArrowKind_38 -> T_Quantity_8
d_quantity_44 v0
  = case coe v0 of
      C_mk'45'kind_48 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Grade.ArrowKind.purity
d_purity_46 :: T_ArrowKind_38 -> T_Purity_28
d_purity_46 v0
  = case coe v0 of
      C_mk'45'kind_48 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Grade.pureK
d_pureK_50 :: T_Quantity_8 -> T_ArrowKind_38
d_pureK_50 v0 = coe C_mk'45'kind_48 (coe v0) (coe C_pure_30)
-- Once.Spec.Type.Grade.effK
d_effK_54 :: T_ArrowKind_38
d_effK_54 = coe C_mk'45'kind_48 (coe C_Many_14) (coe C_eff_32)
