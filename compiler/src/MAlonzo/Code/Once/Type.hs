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
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
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
  = C_K_110 T_Type_108 | C_Id_112 |
    C__'8853'__114 T_Functor_106 T_Functor_106 |
    C__'8855'__116 T_Functor_106 T_Functor_106
-- Once.Type.Type
d_Type_108 = ()
data T_Type_108
  = C_Unit_118 | C_Void_120 | C__'42'__122 T_Type_108 T_Type_108 |
    C__'43'__124 T_Type_108 T_Type_108 |
    C__'8658''91'_'93'__126 T_Type_108 T_ArrowKind_40 T_Type_108 |
    C_μ'45'type_128 T_Functor_106 | C_ν'45'type_130 T_Functor_106 |
    C_Int_132 | C_Float_134 | C_Str_136 | C_Buffer_138
-- Once.Type._⊸_
d__'8888'__140 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8888'__140 v0 v1
  = coe
      C__'8658''91'_'93'__126 (coe v0)
      (coe C_mk'45'kind_50 (coe C_One_8) (coe C_pure_34)) (coe v1)
-- Once.Type._⇒_
d__'8658'__146 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8658'__146 v0 v1
  = coe
      C__'8658''91'_'93'__126 (coe v0)
      (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_pure_34)) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__152 :: T_Type_108 -> T_Type_108 -> T_Type_108
d__'8658''8320'__152 v0 v1
  = coe
      C__'8658''91'_'93'__126 (coe v0)
      (coe C_mk'45'kind_50 (coe C_Zero_6) (coe C_pure_34)) (coe v1)
-- Once.Type.isUnit?
d_isUnit'63'_160 ::
  T_Type_108 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isUnit'63'_160 v0
  = case coe v0 of
      C_Unit_118
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      C_Void_120
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'42'__122 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'43'__124 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'8658''91'_'93'__126 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_μ'45'type_128 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_ν'45'type_130 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Int_132
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Float_134
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Str_136
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Buffer_138
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_162 :: T_Functor_106 -> T_Type_108 -> T_Type_108
d_'10214'_'10215'T_162 v0 v1
  = case coe v0 of
      C_K_110 v2 -> coe v2
      C_Id_112 -> coe v1
      C__'8853'__114 v2 v3
        -> coe
             C__'43'__124 (coe d_'10214'_'10215'T_162 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_162 (coe v3) (coe v1))
      C__'8855'__116 v2 v3
        -> coe
             C__'42'__122 (coe d_'10214'_'10215'T_162 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_162 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_182 :: T_Functor_106
d_NatF_182
  = coe C__'8853'__114 (coe C_K_110 (coe C_Unit_118)) (coe C_Id_112)
-- Once.Type.ListF
d_ListF_184 :: T_Type_108 -> T_Functor_106
d_ListF_184 v0
  = coe
      C__'8853'__114 (coe C_K_110 (coe C_Unit_118))
      (coe C__'8855'__116 (coe C_K_110 (coe v0)) (coe C_Id_112))
-- Once.Type.TreeF
d_TreeF_188 :: T_Type_108 -> T_Functor_106
d_TreeF_188 v0
  = coe
      C__'8853'__114 (coe C_K_110 (coe v0))
      (coe C__'8855'__116 (coe C_Id_112) (coe C_Id_112))
-- Once.Type.FitsInReg
d_FitsInReg_192 a0 = ()
data T_FitsInReg_192 = C_fits'45'int_194 | C_fits'45'float_196
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_200 :: T_Type_108 -> Maybe T_FitsInReg_192
d_fits'45'in'45'reg'63'_200 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_Int_132
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_194)
         C_Float_134
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_196)
         _ -> coe v1)
-- Once.Type.showType
d_showType_202 ::
  T_Type_108 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_202 v0
  = case coe v0 of
      C_Unit_118 -> coe ("Unit" :: Data.Text.Text)
      C_Void_120 -> coe ("Void" :: Data.Text.Text)
      C__'42'__122 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_202 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_202 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__124 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_202 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_202 (coe v2)) (")" :: Data.Text.Text))))
      C__'8658''91'_'93'__126 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    C_pure_34
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_202 (coe v1))
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
                                          (d_showType_202 (coe v3)) (")" :: Data.Text.Text))))))
                    C_eff_36
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_202 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_202 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_204 (coe v1))
      C_ν'45'type_130 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_204 (coe v1))
      C_Int_132 -> coe ("Int" :: Data.Text.Text)
      C_Float_134 -> coe ("Float" :: Data.Text.Text)
      C_Str_136 -> coe ("String" :: Data.Text.Text)
      C_Buffer_138 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_204 ::
  T_Functor_106 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_204 v0
  = case coe v0 of
      C_K_110 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_202 (coe v1)) (")" :: Data.Text.Text))
      C_Id_112 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__114 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_204 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_204 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_204 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_204 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.PolyFunctor
d_PolyFunctor_238 = ()
data T_PolyFunctor_238
  = C_PK_242 T_PolyType_240 | C_PId_244 |
    C__P'8853'__246 T_PolyFunctor_238 T_PolyFunctor_238 |
    C__P'8855'__248 T_PolyFunctor_238 T_PolyFunctor_238
-- Once.Type.PolyType
d_PolyType_240 = ()
data T_PolyType_240
  = C_PUnit_250 | C_PVoid_252 |
    C__P'42'__254 T_PolyType_240 T_PolyType_240 |
    C__P'43'__256 T_PolyType_240 T_PolyType_240 |
    C__P'8658''91'_'93'__258 T_PolyType_240 T_Quantity_4
                             T_PolyType_240 |
    C_PEff_260 T_PolyType_240 T_PolyType_240 |
    C_Pμ'45'type_262 T_PolyFunctor_238 |
    C_Pν'45'type_264 T_PolyFunctor_238 | C_PInt_266 | C_PFloat_268 |
    C_PStr_270 | C_PBuffer_272 |
    C_PTVar_274 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_276 :: T_PolyFunctor_238 -> ()
d_GroundF_276 = erased
-- Once.Type.Ground
d_Ground_278 :: T_PolyType_240 -> ()
d_Ground_278 = erased
-- Once.Type.extractGroundF
d_extractGroundF_312 ::
  T_PolyFunctor_238 -> AgdaAny -> T_Functor_106
d_extractGroundF_312 v0 v1
  = case coe v0 of
      C_PK_242 v2
        -> coe C_K_110 (coe d_extractGround_316 (coe v2) (coe v1))
      C_PId_244 -> coe C_Id_112
      C__P'8853'__246 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__114 (coe d_extractGroundF_312 (coe v2) (coe v4))
                    (coe d_extractGroundF_312 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__248 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__116 (coe d_extractGroundF_312 (coe v2) (coe v4))
                    (coe d_extractGroundF_312 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_316 :: T_PolyType_240 -> AgdaAny -> T_Type_108
d_extractGround_316 v0 v1
  = case coe v0 of
      C_PUnit_250 -> coe C_Unit_118
      C_PVoid_252 -> coe C_Void_120
      C__P'42'__254 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__122 (coe d_extractGround_316 (coe v2) (coe v4))
                    (coe d_extractGround_316 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__256 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__124 (coe d_extractGround_316 (coe v2) (coe v4))
                    (coe d_extractGround_316 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__258 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_316 (coe v2) (coe v5))
                    (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))
                    (coe d_extractGround_316 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_260 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_316 (coe v2) (coe v4))
                    (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))
                    (coe d_extractGround_316 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_262 v2
        -> coe C_μ'45'type_128 (coe d_extractGroundF_312 (coe v2) (coe v1))
      C_Pν'45'type_264 v2
        -> coe C_ν'45'type_130 (coe d_extractGroundF_312 (coe v2) (coe v1))
      C_PInt_266 -> coe C_Int_132
      C_PFloat_268 -> coe C_Float_134
      C_PStr_270 -> coe C_Str_136
      C_PBuffer_272 -> coe C_Buffer_138
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embedFunctor
d_embedFunctor_380 :: T_Functor_106 -> T_PolyFunctor_238
d_embedFunctor_380 v0
  = case coe v0 of
      C_K_110 v1 -> coe C_PK_242 (coe d_embed_382 (coe v1))
      C_Id_112 -> coe C_PId_244
      C__'8853'__114 v1 v2
        -> coe
             C__P'8853'__246 (coe d_embedFunctor_380 (coe v1))
             (coe d_embedFunctor_380 (coe v2))
      C__'8855'__116 v1 v2
        -> coe
             C__P'8855'__248 (coe d_embedFunctor_380 (coe v1))
             (coe d_embedFunctor_380 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_382 :: T_Type_108 -> T_PolyType_240
d_embed_382 v0
  = case coe v0 of
      C_Unit_118 -> coe C_PUnit_250
      C_Void_120 -> coe C_PVoid_252
      C__'42'__122 v1 v2
        -> coe
             C__P'42'__254 (coe d_embed_382 (coe v1)) (coe d_embed_382 (coe v2))
      C__'43'__124 v1 v2
        -> coe
             C__P'43'__256 (coe d_embed_382 (coe v1)) (coe d_embed_382 (coe v2))
      C__'8658''91'_'93'__126 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    C_pure_34
                      -> coe
                           C__P'8658''91'_'93'__258 (coe d_embed_382 (coe v1)) (coe v4)
                           (coe d_embed_382 (coe v3))
                    C_eff_36
                      -> coe
                           C_PEff_260 (coe d_embed_382 (coe v1)) (coe d_embed_382 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe C_Pμ'45'type_262 (coe d_embedFunctor_380 (coe v1))
      C_ν'45'type_130 v1
        -> coe C_Pν'45'type_264 (coe d_embedFunctor_380 (coe v1))
      C_Int_132 -> coe C_PInt_266
      C_Float_134 -> coe C_PFloat_268
      C_Str_136 -> coe C_PStr_270
      C_Buffer_138 -> coe C_PBuffer_272
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_420 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_420 ~v0 ~v1 v2 v3 = du_both'45'ground_420 v2 v3
du_both'45'ground_420 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_420 v0 v1
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
d_isGroundF_428 ::
  T_PolyFunctor_238 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_428 v0
  = case coe v0 of
      C_PK_242 v1 -> coe d_isGround_432 (coe v1)
      C_PId_244
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__246 v1 v2
        -> coe
             du_both'45'ground_420 (coe d_isGroundF_428 (coe v1))
             (coe d_isGroundF_428 (coe v2))
      C__P'8855'__248 v1 v2
        -> coe
             du_both'45'ground_420 (coe d_isGroundF_428 (coe v1))
             (coe d_isGroundF_428 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_432 ::
  T_PolyType_240 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_432 v0
  = case coe v0 of
      C_PUnit_250
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_252
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__254 v1 v2
        -> coe
             du_both'45'ground_420 (coe d_isGround_432 (coe v1))
             (coe d_isGround_432 (coe v2))
      C__P'43'__256 v1 v2
        -> coe
             du_both'45'ground_420 (coe d_isGround_432 (coe v1))
             (coe d_isGround_432 (coe v2))
      C__P'8658''91'_'93'__258 v1 v2 v3
        -> coe
             du_both'45'ground_420 (coe d_isGround_432 (coe v1))
             (coe d_isGround_432 (coe v3))
      C_PEff_260 v1 v2
        -> coe
             du_both'45'ground_420 (coe d_isGround_432 (coe v1))
             (coe d_isGround_432 (coe v2))
      C_Pμ'45'type_262 v1 -> coe d_isGroundF_428 (coe v1)
      C_Pν'45'type_264 v1 -> coe d_isGroundF_428 (coe v1)
      C_PInt_266
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_268
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PStr_270
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PBuffer_272
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_274 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_464 ::
  T_PolyType_240 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_464 v0
  = case coe v0 of
      C_PUnit_250 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_252 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__254 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_464 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_464 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__256 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_464 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_464 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__258 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_464 (coe v1))
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
                            (d_showPolyType_464 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_260 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_464 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_464 (coe v2))))
      C_Pμ'45'type_262 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_466 (coe v1))
      C_Pν'45'type_264 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_466 (coe v1))
      C_PInt_266 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_268 -> coe ("Float" :: Data.Text.Text)
      C_PStr_270 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_272 -> coe ("Buffer" :: Data.Text.Text)
      C_PTVar_274 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_466 ::
  T_PolyFunctor_238 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_466 v0
  = case coe v0 of
      C_PK_242 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_464 (coe v1)) (")" :: Data.Text.Text))
      C_PId_244 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__246 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_466 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_466 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__248 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_466 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_466 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_502 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_502 v0 v1
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
d_purityEqBool_504 :: T_Purity_32 -> T_Purity_32 -> Bool
d_purityEqBool_504 v0 v1
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
-- Once.Type.typeEqBool
d_typeEqBool_506 :: T_Type_108 -> T_Type_108 -> Bool
d_typeEqBool_506 v0 v1
  = case coe v0 of
      C_Unit_118
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Void_120
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'__122 v2 v3
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_506 (coe v2) (coe v4))
                    (coe d_typeEqBool_506 (coe v3) (coe v5))
             C__'43'__124 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'43'__124 v2 v3
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_506 (coe v2) (coe v4))
                    (coe d_typeEqBool_506 (coe v3) (coe v5))
             C__'8658''91'_'93'__126 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v5 v6 v7
               -> case coe v3 of
                    C_mk'45'kind_50 v8 v9
                      -> case coe v6 of
                           C_mk'45'kind_50 v10 v11
                             -> coe
                                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                  (coe d_quantityEqBool_502 (coe v8) (coe v10))
                                  (coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_purityEqBool_504 (coe v9) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_typeEqBool_506 (coe v2) (coe v5))
                                        (coe d_typeEqBool_506 (coe v4) (coe v7))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_μ'45'type_128 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v5 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v2
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v3 -> coe d_functorEqBool_508 (coe v2) (coe v3)
             C_ν'45'type_130 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ν'45'type_130 v2
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v3 -> coe d_functorEqBool_508 (coe v2) (coe v3)
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Int_132
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Float_134
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Str_136
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Buffer_138
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'42'__122 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'43'__124 v2 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8658''91'_'93'__126 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_μ'45'type_128 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ν'45'type_130 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.functorEqBool
d_functorEqBool_508 :: T_Functor_106 -> T_Functor_106 -> Bool
d_functorEqBool_508 v0 v1
  = case coe v0 of
      C_K_110 v2
        -> case coe v1 of
             C_K_110 v3 -> coe d_typeEqBool_506 (coe v2) (coe v3)
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__114 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__116 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Id_112
        -> case coe v1 of
             C_K_110 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C__'8853'__114 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__116 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8853'__114 v2 v3
        -> case coe v1 of
             C_K_110 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__114 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_508 (coe v2) (coe v4))
                    (coe d_functorEqBool_508 (coe v3) (coe v5))
             C__'8855'__116 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'__116 v2 v3
        -> case coe v1 of
             C_K_110 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8853'__114 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C__'8855'__116 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_508 (coe v2) (coe v4))
                    (coe d_functorEqBool_508 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Subst
d_Subst_570 :: ()
d_Subst_570 = erased
-- Once.Type._._×'_
d__'215'''__576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'''__576 = erased
-- Once.Type.lookupSubst
d_lookupSubst_578 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_Type_108
d_lookupSubst_578 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupSubst_578 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extendSubst
d_extendSubst_612 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_612 v0 v1 v2
  = let v3 = d_lookupSubst_578 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_typeEqBool_506 (coe v1) (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
                   (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.maybe-bind
d_maybe'45'bind_646 ::
  () ->
  () -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'bind_646 ~v0 ~v1 v2 v3 = du_maybe'45'bind_646 v2 v3
du_maybe'45'bind_646 ::
  (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'bind_646 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.maybe-pair
d_maybe'45'pair_658 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'pair_658 ~v0 ~v1 ~v2 v3 v4 v5
  = du_maybe'45'pair_658 v3 v4 v5
du_maybe'45'pair_658 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'pair_658 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.if-true-maybe
d_if'45'true'45'maybe_668 ::
  () -> Bool -> Maybe AgdaAny -> Maybe AgdaAny
d_if'45'true'45'maybe_668 ~v0 v1 v2
  = du_if'45'true'45'maybe_668 v1 v2
du_if'45'true'45'maybe_668 ::
  Bool -> Maybe AgdaAny -> Maybe AgdaAny
du_if'45'true'45'maybe_668 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Type.instantiate
d_instantiate_672 ::
  T_PolyType_240 ->
  T_Type_108 -> Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_672 v0 v1
  = coe
      d_instantiateAcc_674 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.instantiateAcc
d_instantiateAcc_674 ::
  T_PolyType_240 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_674 v0 v1 v2
  = case coe v0 of
      C_PUnit_250
        -> case coe v1 of
             C_Unit_118
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PVoid_252
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'42'__254 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v5 v6
               -> coe
                    du_maybe'45'bind_646 (coe d_instantiateAcc_674 (coe v4) (coe v6))
                    (coe d_instantiateAcc_674 (coe v3) (coe v5) (coe v2))
             C__'43'__124 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__256 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v5 v6
               -> coe
                    du_maybe'45'bind_646 (coe d_instantiateAcc_674 (coe v4) (coe v6))
                    (coe d_instantiateAcc_674 (coe v3) (coe v5) (coe v2))
             C__'8658''91'_'93'__126 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__258 v3 v4 v5
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v6 v7 v8
               -> case coe v7 of
                    C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           C_pure_34
                             -> coe
                                  du_if'45'true'45'maybe_668
                                  (coe d_quantityEqBool_502 (coe v4) (coe v9))
                                  (coe
                                     du_maybe'45'bind_646
                                     (coe d_instantiateAcc_674 (coe v5) (coe v8))
                                     (coe d_instantiateAcc_674 (coe v3) (coe v6) (coe v2)))
                           C_eff_36 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_μ'45'type_128 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_260 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v5 v6 v7
               -> case coe v6 of
                    C_mk'45'kind_50 v8 v9
                      -> case coe v9 of
                           C_pure_34 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           C_eff_36
                             -> coe
                                  du_maybe'45'bind_646 (coe d_instantiateAcc_674 (coe v4) (coe v7))
                                  (coe d_instantiateAcc_674 (coe v3) (coe v5) (coe v2))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_μ'45'type_128 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_262 v3
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v4
               -> coe d_instantiateFunctor_676 (coe v3) (coe v4) (coe v2)
             C_ν'45'type_130 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pν'45'type_264 v3
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v4
               -> coe d_instantiateFunctor_676 (coe v3) (coe v4) (coe v2)
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PInt_266
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PFloat_268
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PStr_270
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PBuffer_272
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8658''91'_'93'__126 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_μ'45'type_128 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_ν'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PTVar_274 v3 -> coe d_extendSubst_612 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.instantiateFunctor
d_instantiateFunctor_676 ::
  T_PolyFunctor_238 ->
  T_Functor_106 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_676 v0 v1 v2
  = case coe v0 of
      C_PK_242 v3
        -> case coe v1 of
             C_K_110 v4 -> coe d_instantiateAcc_674 (coe v3) (coe v4) (coe v2)
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PId_244
        -> case coe v1 of
             C_K_110 v3 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C__'8853'__114 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8853'__246 v3 v4
        -> case coe v1 of
             C_K_110 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v5 v6
               -> coe
                    du_maybe'45'bind_646
                    (coe d_instantiateFunctor_676 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_676 (coe v3) (coe v5) (coe v2))
             C__'8855'__116 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__248 v3 v4
        -> case coe v1 of
             C_K_110 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v5 v6
               -> coe
                    du_maybe'45'bind_646
                    (coe d_instantiateFunctor_676 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_676 (coe v3) (coe v5) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubst
d_applySubst_784 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyType_240 -> Maybe T_Type_108
d_applySubst_784 v0 v1
  = case coe v1 of
      C_PUnit_250
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_118)
      C_PVoid_252
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_120)
      C__P'42'__254 v2 v3
        -> coe
             du_maybe'45'pair_658 (coe C__'42'__122)
             (coe d_applySubst_784 (coe v0) (coe v2))
             (coe d_applySubst_784 (coe v0) (coe v3))
      C__P'43'__256 v2 v3
        -> coe
             du_maybe'45'pair_658 (coe C__'43'__124)
             (coe d_applySubst_784 (coe v0) (coe v2))
             (coe d_applySubst_784 (coe v0) (coe v3))
      C__P'8658''91'_'93'__258 v2 v3 v4
        -> coe
             du_maybe'45'pair_658
             (coe
                (\ v5 ->
                   coe
                     C__'8658''91'_'93'__126 (coe v5)
                     (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))))
             (coe d_applySubst_784 (coe v0) (coe v2))
             (coe d_applySubst_784 (coe v0) (coe v4))
      C_PEff_260 v2 v3
        -> coe
             du_maybe'45'pair_658
             (coe
                (\ v4 ->
                   coe
                     C__'8658''91'_'93'__126 (coe v4)
                     (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))))
             (coe d_applySubst_784 (coe v0) (coe v2))
             (coe d_applySubst_784 (coe v0) (coe v3))
      C_Pμ'45'type_262 v2
        -> coe
             du_maybe'45'bind_646
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe C_μ'45'type_128 (coe v3))))
             (coe d_applySubstFunctor_786 (coe v0) (coe v2))
      C_Pν'45'type_264 v2
        -> coe
             du_maybe'45'bind_646
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe C_ν'45'type_130 (coe v3))))
             (coe d_applySubstFunctor_786 (coe v0) (coe v2))
      C_PInt_266
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_132)
      C_PFloat_268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_134)
      C_PStr_270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_136)
      C_PBuffer_272
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_138)
      C_PTVar_274 v2 -> coe d_lookupSubst_578 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubstFunctor
d_applySubstFunctor_786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyFunctor_238 -> Maybe T_Functor_106
d_applySubstFunctor_786 v0 v1
  = case coe v1 of
      C_PK_242 v2
        -> coe
             du_maybe'45'bind_646
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_110 (coe v3))))
             (coe d_applySubst_784 (coe v0) (coe v2))
      C_PId_244
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_112)
      C__P'8853'__246 v2 v3
        -> coe
             du_maybe'45'pair_658 (coe C__'8853'__114)
             (coe d_applySubstFunctor_786 (coe v0) (coe v2))
             (coe d_applySubstFunctor_786 (coe v0) (coe v3))
      C__P'8855'__248 v2 v3
        -> coe
             du_maybe'45'pair_658 (coe C__'8855'__116)
             (coe d_applySubstFunctor_786 (coe v0) (coe v2))
             (coe d_applySubstFunctor_786 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.schemaArrowCodomain
d_schemaArrowCodomain_856 ::
  T_PolyType_240 -> T_Type_108 -> Maybe T_Type_108
d_schemaArrowCodomain_856 v0 v1
  = case coe v0 of
      C_PUnit_250 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PVoid_252 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'42'__254 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'43'__256 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'8658''91'_'93'__258 v2 v3 v4
        -> coe
             du_maybe'45'bind_646
             (coe (\ v5 -> d_applySubst_784 (coe v5) (coe v4)))
             (coe d_instantiate_672 (coe v2) (coe v1))
      C_PEff_260 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_Pμ'45'type_262 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_Pν'45'type_264 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PInt_266 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PFloat_268 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PStr_270 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PBuffer_272 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PTVar_274 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
