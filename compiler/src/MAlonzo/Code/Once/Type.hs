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

module MAlonzo.Code.Once.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Type.Quantity
d_Quantity_4 = ()
data T_Quantity_4 = C_Zero_6 | C_One_8 | C_Many_10
-- Once.Type._+q_
d__'43'q__12 :: T_Quantity_4 -> T_Quantity_4 -> T_Quantity_4
d__'43'q__12 v0 v1
  = case coe v0 of
      C_Zero_6 -> coe v1
      C_One_8
        -> case coe v1 of
             C_Zero_6 -> coe v0
             C_One_8 -> coe C_Many_10
             C_Many_10 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_10 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._*q_
d__'42'q__16 :: T_Quantity_4 -> T_Quantity_4 -> T_Quantity_4
d__'42'q__16 v0 v1
  = case coe v0 of
      C_Zero_6 -> coe v0
      C_One_8 -> coe v1
      C_Many_10
        -> case coe v1 of
             C_Zero_6 -> coe v1
             C_One_8 -> coe v0
             C_Many_10 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≟q_
d__'8799'q__26 ::
  T_Quantity_4 ->
  T_Quantity_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'q__26 v0 v1
  = case coe v0 of
      C_Zero_6
        -> case coe v1 of
             C_Zero_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_One_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Many_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_One_8
        -> case coe v1 of
             C_Zero_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_One_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Many_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_10
        -> case coe v1 of
             C_Zero_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_One_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Many_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≤q_
d__'8804'q__28 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d__'8804'q__28 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         C_One_8
           -> case coe v1 of
                C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Many_10
           -> case coe v1 of
                C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.showQuantity
d_showQuantity_30 ::
  T_Quantity_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_30 v0
  = case coe v0 of
      C_Zero_6 -> coe ("0" :: Data.Text.Text)
      C_One_8 -> coe ("1" :: Data.Text.Text)
      C_Many_10 -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Type
d_Type_32 = ()
data T_Type_32
  = C_Unit_34 | C_Void_36 | C__'42'__38 T_Type_32 T_Type_32 |
    C__'43'__40 T_Type_32 T_Type_32 |
    C__'8658''91'_'93'__42 T_Type_32 T_Quantity_4 T_Type_32 |
    C_Eff_44 T_Type_32 T_Type_32 | C_Fix_46 T_Type_32 | C_Int_48 |
    C_Float_50 | C_Str_52 | C_Buffer_54 |
    C_TVar_56 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type._⊸_
d__'8888'__58 :: T_Type_32 -> T_Type_32 -> T_Type_32
d__'8888'__58 v0 v1
  = coe C__'8658''91'_'93'__42 (coe v0) (coe C_One_8) (coe v1)
-- Once.Type._⇒_
d__'8658'__64 :: T_Type_32 -> T_Type_32 -> T_Type_32
d__'8658'__64 v0 v1
  = coe C__'8658''91'_'93'__42 (coe v0) (coe C_Many_10) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__70 :: T_Type_32 -> T_Type_32 -> T_Type_32
d__'8658''8320'__70 v0 v1
  = coe C__'8658''91'_'93'__42 (coe v0) (coe C_Zero_6) (coe v1)
-- Once.Type.IO
d_IO_76 :: T_Type_32 -> T_Type_32
d_IO_76 v0 = coe C_Eff_44 (coe C_Unit_34) (coe v0)
