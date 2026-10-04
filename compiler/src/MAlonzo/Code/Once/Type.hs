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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
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
d__'8799'q__22 ::
  T_Quantity_4 ->
  T_Quantity_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'q__22 v0 v1
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
-- Once.Type._⊔q_
d__'8852'q__24 :: T_Quantity_4 -> T_Quantity_4 -> T_Quantity_4
d__'8852'q__24 v0 v1
  = case coe v0 of
      C_Zero_6 -> coe v1
      C_One_8
        -> case coe v1 of
             C_Zero_6 -> coe v0
             C_One_8 -> coe v1
             C_Many_10 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_10 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≤q_
d__'8804'q__28 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d__'8804'q__28 v0 v1
  = case coe v0 of
      C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_One_8
        -> case coe v1 of
             C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_10
        -> case coe v1 of
             C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showQuantity
d_showQuantity_30 ::
  T_Quantity_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_30 v0
  = case coe v0 of
      C_Zero_6 -> coe ("0" :: Data.Text.Text)
      C_One_8 -> coe ("1" :: Data.Text.Text)
      C_Many_10 -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Purity
d_Purity_32 = ()
data T_Purity_32 = C_pure_34 | C_eff_36
-- Once.Type.showPurity
d_showPurity_38 ::
  T_Purity_32 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPurity_38 v0
  = case coe v0 of
      C_pure_34 -> coe ("pure" :: Data.Text.Text)
      C_eff_36 -> coe ("eff" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ArrowKind
d_ArrowKind_40 = ()
data T_ArrowKind_40 = C_mk'45'kind_50 T_Quantity_4 T_Purity_32
-- Once.Type.ArrowKind.quantity
d_quantity_46 :: T_ArrowKind_40 -> T_Quantity_4
d_quantity_46 v0
  = case coe v0 of
      C_mk'45'kind_50 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ArrowKind.purity
d_purity_48 :: T_ArrowKind_40 -> T_Purity_32
d_purity_48 v0
  = case coe v0 of
      C_mk'45'kind_50 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showArrowKind
d_showArrowKind_52 ::
  T_ArrowKind_40 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArrowKind_52 v0
  = case coe v0 of
      C_mk'45'kind_50 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showQuantity_30 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("," :: Data.Text.Text) (d_showPurity_38 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.pureK
d_pureK_58 :: T_Quantity_4 -> T_ArrowKind_40
d_pureK_58 v0 = coe C_mk'45'kind_50 (coe v0) (coe C_pure_34)
-- Once.Type.effK
d_effK_62 :: T_ArrowKind_40
d_effK_62 = coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36)
-- Once.Type._⊔p_
d__'8852'p__64 :: T_Purity_32 -> T_Purity_32 -> T_Purity_32
d__'8852'p__64 v0 v1
  = case coe v0 of
      C_pure_34 -> coe v1
      C_eff_36 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≟p_
d__'8799'p__72 ::
  T_Purity_32 ->
  T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'p__72 v0 v1
  = case coe v0 of
      C_pure_34
        -> case coe v1 of
             C_pure_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_eff_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_36
        -> case coe v1 of
             C_pure_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_eff_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.≟k-aux
d_'8799'k'45'aux_82 ::
  T_Quantity_4 ->
  T_Quantity_4 ->
  T_Purity_32 ->
  T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'k'45'aux_82 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'k'45'aux_82 v4 v5
du_'8799'k'45'aux_82 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'k'45'aux_82 v0 v1
  = let v2
          = case coe v1 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
                -> coe
                     seq (coe v2)
                     (coe
                        seq (coe v3)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> let v5
                    = case coe v1 of
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                          -> case coe v5 of
                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                 -> case coe v6 of
                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                        -> coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                      _ -> coe v2
                               _ -> coe v2
                        _ -> MAlonzo.RTE.mazUnreachableError in
              coe
                (if coe v3
                   then case coe v1 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                            -> if coe v6
                                 then case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                          -> case coe v7 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v6)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                         erased)
                                               _ -> coe v5
                                        _ -> coe v5
                                 else (case coe v7 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                           -> coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                         _ -> coe v5)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   else (case coe v4 of
                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                             -> coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v3)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                           _ -> coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type._≟k_
d__'8799'k__96 ::
  T_ArrowKind_40 ->
  T_ArrowKind_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'k__96 v0 v1
  = case coe v0 of
      C_mk'45'kind_50 v2 v3
        -> case coe v1 of
             C_mk'45'kind_50 v4 v5
               -> coe
                    du_'8799'k'45'aux_82 (coe d__'8799'q__22 (coe v2) (coe v4))
                    (coe d__'8799'p__72 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Functor
d_Functor_106 = ()
data T_Functor_106
  = C_K_112 T_Type_108 | C_Id_114 |
    C__'8853'__116 T_Functor_106 T_Functor_106 |
    C__'8855'__118 T_Functor_106 T_Functor_106
-- Once.Type.Type
d_Type_108 = ()
data T_Type_108
  = C_Unit_120 | C_Void_122 | C__'42'__124 T_Type_108 T_Type_108 |
    C__'43'__126 T_Type_108 T_Type_108 |
    C__'8658''91'_'93'__128 T_Type_108 T_ArrowKind_40 T_Type_108 |
    C_μ'45'type_130 T_Functor_106 |
    C_ν'45'type_132 T_Functor_106 T_Purity_32 | C_Int_134 |
    C_Float_136 | C_rigid_138 T_TKind_110 Integer
-- Once.Type.TKind
d_TKind_110 = ()
data T_TKind_110 = C_k'45'base_140 | C_k'45'any_142
-- Once.Type._⊸_
d__'8888'__144 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8888'__144 v0 v1
  = coe
      C__'8658''91'_'93'__128 (coe v0)
      (coe C_mk'45'kind_50 (coe C_One_8) (coe C_pure_34)) (coe v1)
-- Once.Type._⇒_
d__'8658'__150 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8658'__150 v0 v1
  = coe
      C__'8658''91'_'93'__128 (coe v0)
      (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_pure_34)) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__156 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8658''8320'__156 v0 v1
  = coe
      C__'8658''91'_'93'__128 (coe v0)
      (coe C_mk'45'kind_50 (coe C_Zero_6) (coe C_pure_34)) (coe v1)
-- Once.Type.isVoid?
d_isVoid'63'_164 ::
  T_Type_108 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isVoid'63'_164 v0
  = case coe v0 of
      C_Unit_120
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Void_122
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      C__'42'__124 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'43'__126 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'8658''91'_'93'__128 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_μ'45'type_130 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_ν'45'type_132 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Int_134
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Float_136
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_rigid_138 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isUnit?
d_isUnit'63'_168 ::
  T_Type_108 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isUnit'63'_168 v0
  = case coe v0 of
      C_Unit_120
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      C_Void_122
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'42'__124 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'43'__126 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'8658''91'_'93'__128 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_μ'45'type_130 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_ν'45'type_132 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Int_134
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Float_136
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_rigid_138 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_170 :: T_Functor_106 -> T_Type_108 -> T_Type_108
d_'10214'_'10215'T_170 v0 v1
  = case coe v0 of
      C_K_112 v2 -> coe v2
      C_Id_114 -> coe v1
      C__'8853'__116 v2 v3
        -> coe
             C__'43'__126 (coe d_'10214'_'10215'T_170 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_170 (coe v3) (coe v1))
      C__'8855'__118 v2 v3
        -> coe
             C__'42'__124 (coe d_'10214'_'10215'T_170 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_170 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_190 :: T_Functor_106
d_NatF_190
  = coe C__'8853'__116 (coe C_K_112 (coe C_Unit_120)) (coe C_Id_114)
-- Once.Type.ListF
d_ListF_192 :: T_Type_108 -> T_Functor_106
d_ListF_192 v0
  = coe
      C__'8853'__116 (coe C_K_112 (coe C_Unit_120))
      (coe C__'8855'__118 (coe C_K_112 (coe v0)) (coe C_Id_114))
-- Once.Type.TreeF
d_TreeF_196 :: T_Type_108 -> T_Functor_106
d_TreeF_196 v0
  = coe
      C__'8853'__116 (coe C_K_112 (coe v0))
      (coe C__'8855'__118 (coe C_Id_114) (coe C_Id_114))
-- Once.Type.FitsInReg
d_FitsInReg_200 a0 = ()
data T_FitsInReg_200 = C_fits'45'int_202 | C_fits'45'float_204
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_208 :: T_Type_108 -> Maybe T_FitsInReg_200
d_fits'45'in'45'reg'63'_208 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_Int_134
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_202)
         C_Float_136
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_204)
         _ -> coe v1)
-- Once.Type.showType
d_showType_210 ::
  T_Type_108 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_210 v0
  = case coe v0 of
      C_Unit_120 -> coe ("Unit" :: Data.Text.Text)
      C_Void_122 -> coe ("Void" :: Data.Text.Text)
      C__'42'__124 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_210 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_210 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__126 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_210 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_210 (coe v2)) (")" :: Data.Text.Text))))
      C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    C_pure_34
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_210 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_showQuantity_30 (coe v4))
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("\8594 " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (d_showType_210 (coe v3)) (")" :: Data.Text.Text))))))
                    C_eff_36
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_210 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_210 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_130 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_212 (coe v1))
      C_ν'45'type_132 v1 v2
        -> case coe v2 of
             C_pure_34
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showFunctor_212 (coe v1))
             C_eff_36
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Eff " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showFunctor_212 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Int_134 -> coe ("Int" :: Data.Text.Text)
      C_Float_136 -> coe ("Float" :: Data.Text.Text)
      C_rigid_138 v1 v2
        -> case coe v1 of
             C_k'45'base_140
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'b" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             C_k'45'any_142
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'a" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_212 ::
  T_Functor_106 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_212 v0
  = case coe v0 of
      C_K_112 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_210 (coe v1)) (")" :: Data.Text.Text))
      C_Id_114 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_212 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_212 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_212 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_212 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.PolyFunctor
d_PolyFunctor_252 = ()
data T_PolyFunctor_252
  = C_PK_256 T_PolyType_254 | C_PId_258 |
    C__P'8853'__260 T_PolyFunctor_252 T_PolyFunctor_252 |
    C__P'8855'__262 T_PolyFunctor_252 T_PolyFunctor_252
-- Once.Type.PolyType
d_PolyType_254 = ()
data T_PolyType_254
  = C_PUnit_264 | C_PVoid_266 |
    C__P'42'__268 T_PolyType_254 T_PolyType_254 |
    C__P'43'__270 T_PolyType_254 T_PolyType_254 |
    C__P'8658''91'_'93'__272 T_PolyType_254 T_Quantity_4
                             T_PolyType_254 |
    C_PEff_274 T_PolyType_254 T_PolyType_254 |
    C_Pμ'45'type_276 T_PolyFunctor_252 |
    C_Pν'45'type_278 T_PolyFunctor_252 T_Purity_32 | C_PInt_280 |
    C_PFloat_282 |
    C_PTVar_284 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_286 :: T_PolyFunctor_252 -> ()
d_GroundF_286 = erased
-- Once.Type.Ground
d_Ground_288 :: T_PolyType_254 -> ()
d_Ground_288 = erased
-- Once.Type.extractGroundF
d_extractGroundF_322 ::
  T_PolyFunctor_252 -> AgdaAny -> T_Functor_106
d_extractGroundF_322 v0 v1
  = case coe v0 of
      C_PK_256 v2
        -> coe C_K_112 (coe d_extractGround_326 (coe v2) (coe v1))
      C_PId_258 -> coe C_Id_114
      C__P'8853'__260 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__116 (coe d_extractGroundF_322 (coe v2) (coe v4))
                    (coe d_extractGroundF_322 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__262 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__118 (coe d_extractGroundF_322 (coe v2) (coe v4))
                    (coe d_extractGroundF_322 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_326 :: T_PolyType_254 -> AgdaAny -> T_Type_108
d_extractGround_326 v0 v1
  = case coe v0 of
      C_PUnit_264 -> coe C_Unit_120
      C_PVoid_266 -> coe C_Void_122
      C__P'42'__268 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__124 (coe d_extractGround_326 (coe v2) (coe v4))
                    (coe d_extractGround_326 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__270 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__126 (coe d_extractGround_326 (coe v2) (coe v4))
                    (coe d_extractGround_326 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__272 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__128 (coe d_extractGround_326 (coe v2) (coe v5))
                    (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))
                    (coe d_extractGround_326 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_274 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8658''91'_'93'__128 (coe d_extractGround_326 (coe v2) (coe v4))
                    (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))
                    (coe d_extractGround_326 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_276 v2
        -> coe C_μ'45'type_130 (coe d_extractGroundF_322 (coe v2) (coe v1))
      C_Pν'45'type_278 v2 v3
        -> coe
             C_ν'45'type_132 (coe d_extractGroundF_322 (coe v2) (coe v1))
             (coe v3)
      C_PInt_280 -> coe C_Int_134
      C_PFloat_282 -> coe C_Float_136
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_396 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_396 ~v0 ~v1 v2 v3 = du_both'45'ground_396 v2 v3
du_both'45'ground_396 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_396 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGroundF
d_isGroundF_404 ::
  T_PolyFunctor_252 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_404 v0
  = case coe v0 of
      C_PK_256 v1 -> coe d_isGround_408 (coe v1)
      C_PId_258
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__260 v1 v2
        -> coe
             du_both'45'ground_396 (coe d_isGroundF_404 (coe v1))
             (coe d_isGroundF_404 (coe v2))
      C__P'8855'__262 v1 v2
        -> coe
             du_both'45'ground_396 (coe d_isGroundF_404 (coe v1))
             (coe d_isGroundF_404 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_408 ::
  T_PolyType_254 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_408 v0
  = case coe v0 of
      C_PUnit_264
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_266
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__268 v1 v2
        -> coe
             du_both'45'ground_396 (coe d_isGround_408 (coe v1))
             (coe d_isGround_408 (coe v2))
      C__P'43'__270 v1 v2
        -> coe
             du_both'45'ground_396 (coe d_isGround_408 (coe v1))
             (coe d_isGround_408 (coe v2))
      C__P'8658''91'_'93'__272 v1 v2 v3
        -> coe
             du_both'45'ground_396 (coe d_isGround_408 (coe v1))
             (coe d_isGround_408 (coe v3))
      C_PEff_274 v1 v2
        -> coe
             du_both'45'ground_396 (coe d_isGround_408 (coe v1))
             (coe d_isGround_408 (coe v2))
      C_Pμ'45'type_276 v1 -> coe d_isGroundF_404 (coe v1)
      C_Pν'45'type_278 v1 v2 -> coe d_isGroundF_404 (coe v1)
      C_PInt_280
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_282
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_284 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_440 ::
  T_PolyType_254 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_440 v0
  = case coe v0 of
      C_PUnit_264 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_266 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__268 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_440 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_440 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__270 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_440 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_440 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__272 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_440 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showQuantity_30 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\8594 " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showPolyType_440 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_274 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_440 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_440 (coe v2))))
      C_Pμ'45'type_276 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_442 (coe v1))
      C_Pν'45'type_278 v1 v2
        -> case coe v2 of
             C_pure_34
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showPolyFunctor_442 (coe v1))
             C_eff_36
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Eff " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showPolyFunctor_442 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PInt_280 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_282 -> coe ("Float" :: Data.Text.Text)
      C_PTVar_284 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_442 ::
  T_PolyFunctor_252 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_442 v0
  = case coe v0 of
      C_PK_256 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_440 (coe v1)) (")" :: Data.Text.Text))
      C_PId_258 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__260 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_442 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_442 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__262 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_442 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_442 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_480 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_480 v0 v1
  = case coe v0 of
      C_Zero_6
        -> case coe v1 of
             C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_One_8
        -> case coe v1 of
             C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Many_10
        -> case coe v1 of
             C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.purityEqBool
d_purityEqBool_482 :: T_Purity_32 -> T_Purity_32 -> Bool
d_purityEqBool_482 v0 v1
  = case coe v0 of
      C_pure_34
        -> case coe v1 of
             C_pure_34 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_eff_36 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_36
        -> case coe v1 of
             C_pure_34 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_eff_36 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.tkindEqBool
d_tkindEqBool_484 :: T_TKind_110 -> T_TKind_110 -> Bool
d_tkindEqBool_484 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_k'45'base_140
           -> case coe v1 of
                C_k'45'base_140 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_k'45'any_142
           -> case coe v1 of
                C_k'45'any_142 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.typeEqBool
d_typeEqBool_486 :: T_Type_108 -> T_Type_108 -> Bool
d_typeEqBool_486 v0 v1
  = case coe v0 of
      C_Unit_120
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Void_122
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C__'42'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'__124 v2 v3
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_486 (coe v2) (coe v4))
                    (coe d_typeEqBool_486 (coe v3) (coe v5))
             C__'43'__126 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'43'__126 v2 v3
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_486 (coe v2) (coe v4))
                    (coe d_typeEqBool_486 (coe v3) (coe v5))
             C__'8658''91'_'93'__128 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v5 v6 v7
               -> case coe v3 of
                    C_mk'45'kind_50 v8 v9
                      -> case coe v6 of
                           C_mk'45'kind_50 v10 v11
                             -> coe
                                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                  (coe d_quantityEqBool_480 (coe v8) (coe v10))
                                  (coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_purityEqBool_482 (coe v9) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_typeEqBool_486 (coe v2) (coe v5))
                                        (coe d_typeEqBool_486 (coe v4) (coe v7))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_μ'45'type_130 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_130 v2
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v3 -> coe d_functorEqBool_488 (coe v2) (coe v3)
             C_ν'45'type_132 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ν'45'type_132 v2 v3
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_purityEqBool_482 (coe v3) (coe v5))
                    (coe d_functorEqBool_488 (coe v2) (coe v4))
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Int_134
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_rigid_138 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Float_136
        -> case coe v1 of
             C_Unit_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_122 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__126 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__128 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_132 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_rigid_138 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rigid_138 v2 v3
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
           coe
             (case coe v1 of
                C_rigid_138 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_tkindEqBool_484 (coe v2) (coe v5))
                       (coe eqInt (coe v3) (coe v6))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.functorEqBool
d_functorEqBool_488 :: T_Functor_106 -> T_Functor_106 -> Bool
d_functorEqBool_488 v0 v1
  = case coe v0 of
      C_K_112 v2
        -> case coe v1 of
             C_K_112 v3 -> coe d_typeEqBool_486 (coe v2) (coe v3)
             C_Id_114 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__116 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__118 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Id_114
        -> case coe v1 of
             C_K_112 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_114 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C__'8853'__116 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__118 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8853'__116 v2 v3
        -> case coe v1 of
             C_K_112 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_114 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__116 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_488 (coe v2) (coe v4))
                    (coe d_functorEqBool_488 (coe v3) (coe v5))
             C__'8855'__118 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'__118 v2 v3
        -> case coe v1 of
             C_K_112 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_114 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__116 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__118 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_488 (coe v2) (coe v4))
                    (coe d_functorEqBool_488 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.substPoly
d_substPoly_562 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_Type_108) ->
  T_PolyType_254 -> T_Type_108
d_substPoly_562 v0 v1
  = case coe v1 of
      C_PUnit_264 -> coe C_Unit_120
      C_PVoid_266 -> coe C_Void_122
      C__P'42'__268 v2 v3
        -> coe
             C__'42'__124 (coe d_substPoly_562 (coe v0) (coe v2))
             (coe d_substPoly_562 (coe v0) (coe v3))
      C__P'43'__270 v2 v3
        -> coe
             C__'43'__126 (coe d_substPoly_562 (coe v0) (coe v2))
             (coe d_substPoly_562 (coe v0) (coe v3))
      C__P'8658''91'_'93'__272 v2 v3 v4
        -> coe
             C__'8658''91'_'93'__128 (coe d_substPoly_562 (coe v0) (coe v2))
             (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))
             (coe d_substPoly_562 (coe v0) (coe v4))
      C_PEff_274 v2 v3
        -> coe
             C__'8658''91'_'93'__128 (coe d_substPoly_562 (coe v0) (coe v2))
             (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))
             (coe d_substPoly_562 (coe v0) (coe v3))
      C_Pμ'45'type_276 v2
        -> coe C_μ'45'type_130 (coe d_substPolyF_564 (coe v0) (coe v2))
      C_Pν'45'type_278 v2 v3
        -> coe
             C_ν'45'type_132 (coe d_substPolyF_564 (coe v0) (coe v2)) (coe v3)
      C_PInt_280 -> coe C_Int_134
      C_PFloat_282 -> coe C_Float_136
      C_PTVar_284 v2 -> coe v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.substPolyF
d_substPolyF_564 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_Type_108) ->
  T_PolyFunctor_252 -> T_Functor_106
d_substPolyF_564 v0 v1
  = case coe v1 of
      C_PK_256 v2 -> coe C_K_112 (coe d_substPoly_562 (coe v0) (coe v2))
      C_PId_258 -> coe C_Id_114
      C__P'8853'__260 v2 v3
        -> coe
             C__'8853'__116 (coe d_substPolyF_564 (coe v0) (coe v2))
             (coe d_substPolyF_564 (coe v0) (coe v3))
      C__P'8855'__262 v2 v3
        -> coe
             C__'8855'__118 (coe d_substPolyF_564 (coe v0) (coe v2))
             (coe d_substPolyF_564 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ftv
d_ftv_632 ::
  T_PolyType_254 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftv_632 v0
  = case coe v0 of
      C_PUnit_264 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PVoid_266 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'42'__268 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_632 (coe v1)) (coe d_ftv_632 (coe v2))
      C__P'43'__270 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_632 (coe v1)) (coe d_ftv_632 (coe v2))
      C__P'8658''91'_'93'__272 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_632 (coe v1)) (coe d_ftv_632 (coe v3))
      C_PEff_274 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_632 (coe v1)) (coe d_ftv_632 (coe v2))
      C_Pμ'45'type_276 v1 -> coe d_ftvF_634 (coe v1)
      C_Pν'45'type_278 v1 v2 -> coe d_ftvF_634 (coe v1)
      C_PInt_280 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PFloat_282 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PTVar_284 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ftvF
d_ftvF_634 ::
  T_PolyFunctor_252 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvF_634 v0
  = case coe v0 of
      C_PK_256 v1 -> coe d_ftv_632 (coe v1)
      C_PId_258 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'8853'__260 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_634 (coe v1)) (coe d_ftvF_634 (coe v2))
      C__P'8855'__262 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_634 (coe v1)) (coe d_ftvF_634 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ArrowSchema
d_ArrowSchema_668 a0 a1 a2 a3 = ()
data T_ArrowSchema_668 = C_as'45'pure_674 | C_as'45'eff_680
-- Once.Type.CodVarsInDom
d_CodVarsInDom_682 :: T_PolyType_254 -> T_PolyType_254 -> ()
d_CodVarsInDom_682 = erased
-- Once.Type.IsInstance
d_IsInstance_690 :: T_PolyType_254 -> T_Type_108 -> ()
d_IsInstance_690 = erased
