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
-- Once.Type._≟p_
d__'8799'p__68 ::
  T_Purity_32 ->
  T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'p__68 v0 v1
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
d_'8799'k'45'aux_78 ::
  T_Quantity_4 ->
  T_Quantity_4 ->
  T_Purity_32 ->
  T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'k'45'aux_78 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'k'45'aux_78 v4 v5
du_'8799'k'45'aux_78 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'k'45'aux_78 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
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
                    du_'8799'k'45'aux_78 (coe d__'8799'q__22 (coe v2) (coe v4))
                    (coe d__'8799'p__68 (coe v3) (coe v5))
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
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_158 :: T_Functor_106 -> T_Type_108 -> T_Type_108
d_'10214'_'10215'T_158 v0 v1
  = case coe v0 of
      C_K_110 v2 -> coe v2
      C_Id_112 -> coe v1
      C__'8853'__114 v2 v3
        -> coe
             C__'43'__124 (coe d_'10214'_'10215'T_158 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_158 (coe v3) (coe v1))
      C__'8855'__116 v2 v3
        -> coe
             C__'42'__122 (coe d_'10214'_'10215'T_158 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_158 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_178 :: T_Functor_106
d_NatF_178
  = coe C__'8853'__114 (coe C_K_110 (coe C_Unit_118)) (coe C_Id_112)
-- Once.Type.ListF
d_ListF_180 :: T_Type_108 -> T_Functor_106
d_ListF_180 v0
  = coe
      C__'8853'__114 (coe C_K_110 (coe C_Unit_118))
      (coe C__'8855'__116 (coe C_K_110 (coe v0)) (coe C_Id_112))
-- Once.Type.TreeF
d_TreeF_184 :: T_Type_108 -> T_Functor_106
d_TreeF_184 v0
  = coe
      C__'8853'__114 (coe C_K_110 (coe v0))
      (coe C__'8855'__116 (coe C_Id_112) (coe C_Id_112))
-- Once.Type.IsPrimitive
d_IsPrimitive_188 a0 = ()
data T_IsPrimitive_188
  = C_is'45'unit_190 | C_is'45'int_192 | C_is'45'float_194 |
    C_is'45'str_196 | C_is'45'buffer_198
-- Once.Type.showType
d_showType_200 ::
  T_Type_108 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_200 v0
  = case coe v0 of
      C_Unit_118 -> coe ("Unit" :: Data.Text.Text)
      C_Void_120 -> coe ("Void" :: Data.Text.Text)
      C__'42'__122 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_200 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_200 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__124 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_200 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_200 (coe v2)) (")" :: Data.Text.Text))))
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
                              (d_showType_200 (coe v1))
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
                                          (d_showType_200 (coe v3)) (")" :: Data.Text.Text))))))
                    C_eff_36
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_200 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_200 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_202 (coe v1))
      C_ν'45'type_130 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_202 (coe v1))
      C_Int_132 -> coe ("Int" :: Data.Text.Text)
      C_Float_134 -> coe ("Float" :: Data.Text.Text)
      C_Str_136 -> coe ("String" :: Data.Text.Text)
      C_Buffer_138 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_202 ::
  T_Functor_106 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_202 v0
  = case coe v0 of
      C_K_110 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_200 (coe v1)) (")" :: Data.Text.Text))
      C_Id_112 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__114 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_202 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_202 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_202 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_202 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.PolyFunctor
d_PolyFunctor_236 = ()
data T_PolyFunctor_236
  = C_PK_240 T_PolyType_238 | C_PId_242 |
    C__P'8853'__244 T_PolyFunctor_236 T_PolyFunctor_236 |
    C__P'8855'__246 T_PolyFunctor_236 T_PolyFunctor_236
-- Once.Type.PolyType
d_PolyType_238 = ()
data T_PolyType_238
  = C_PUnit_248 | C_PVoid_250 |
    C__P'42'__252 T_PolyType_238 T_PolyType_238 |
    C__P'43'__254 T_PolyType_238 T_PolyType_238 |
    C__P'8658''91'_'93'__256 T_PolyType_238 T_Quantity_4
                             T_PolyType_238 |
    C_PEff_258 T_PolyType_238 T_PolyType_238 |
    C_Pμ'45'type_260 T_PolyFunctor_236 |
    C_Pν'45'type_262 T_PolyFunctor_236 | C_PInt_264 | C_PFloat_266 |
    C_PStr_268 | C_PBuffer_270 |
    C_PTVar_272 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_274 :: T_PolyFunctor_236 -> ()
d_GroundF_274 = erased
-- Once.Type.Ground
d_Ground_276 :: T_PolyType_238 -> ()
d_Ground_276 = erased
-- Once.Type.extractGroundF
d_extractGroundF_310 ::
  T_PolyFunctor_236 -> AgdaAny -> T_Functor_106
d_extractGroundF_310 v0 v1
  = case coe v0 of
      C_PK_240 v2
        -> coe C_K_110 (coe d_extractGround_314 (coe v2) (coe v1))
      C_PId_242 -> coe C_Id_112
      C__P'8853'__244 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__114 (coe d_extractGroundF_310 (coe v2) (coe v4))
                    (coe d_extractGroundF_310 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__246 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__116 (coe d_extractGroundF_310 (coe v2) (coe v4))
                    (coe d_extractGroundF_310 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_314 :: T_PolyType_238 -> AgdaAny -> T_Type_108
d_extractGround_314 v0 v1
  = case coe v0 of
      C_PUnit_248 -> coe C_Unit_118
      C_PVoid_250 -> coe C_Void_120
      C__P'42'__252 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__122 (coe d_extractGround_314 (coe v2) (coe v4))
                    (coe d_extractGround_314 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__254 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__124 (coe d_extractGround_314 (coe v2) (coe v4))
                    (coe d_extractGround_314 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__256 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_314 (coe v2) (coe v5))
                    (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))
                    (coe d_extractGround_314 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_258 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_314 (coe v2) (coe v4))
                    (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))
                    (coe d_extractGround_314 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_260 v2
        -> coe C_μ'45'type_128 (coe d_extractGroundF_310 (coe v2) (coe v1))
      C_Pν'45'type_262 v2
        -> coe C_ν'45'type_130 (coe d_extractGroundF_310 (coe v2) (coe v1))
      C_PInt_264 -> coe C_Int_132
      C_PFloat_266 -> coe C_Float_134
      C_PStr_268 -> coe C_Str_136
      C_PBuffer_270 -> coe C_Buffer_138
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embedFunctor
d_embedFunctor_378 :: T_Functor_106 -> T_PolyFunctor_236
d_embedFunctor_378 v0
  = case coe v0 of
      C_K_110 v1 -> coe C_PK_240 (coe d_embed_380 (coe v1))
      C_Id_112 -> coe C_PId_242
      C__'8853'__114 v1 v2
        -> coe
             C__P'8853'__244 (coe d_embedFunctor_378 (coe v1))
             (coe d_embedFunctor_378 (coe v2))
      C__'8855'__116 v1 v2
        -> coe
             C__P'8855'__246 (coe d_embedFunctor_378 (coe v1))
             (coe d_embedFunctor_378 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_380 :: T_Type_108 -> T_PolyType_238
d_embed_380 v0
  = case coe v0 of
      C_Unit_118 -> coe C_PUnit_248
      C_Void_120 -> coe C_PVoid_250
      C__'42'__122 v1 v2
        -> coe
             C__P'42'__252 (coe d_embed_380 (coe v1)) (coe d_embed_380 (coe v2))
      C__'43'__124 v1 v2
        -> coe
             C__P'43'__254 (coe d_embed_380 (coe v1)) (coe d_embed_380 (coe v2))
      C__'8658''91'_'93'__126 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    C_pure_34
                      -> coe
                           C__P'8658''91'_'93'__256 (coe d_embed_380 (coe v1)) (coe v4)
                           (coe d_embed_380 (coe v3))
                    C_eff_36
                      -> coe
                           C_PEff_258 (coe d_embed_380 (coe v1)) (coe d_embed_380 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe C_Pμ'45'type_260 (coe d_embedFunctor_378 (coe v1))
      C_ν'45'type_130 v1
        -> coe C_Pν'45'type_262 (coe d_embedFunctor_378 (coe v1))
      C_Int_132 -> coe C_PInt_264
      C_Float_134 -> coe C_PFloat_266
      C_Str_136 -> coe C_PStr_268
      C_Buffer_138 -> coe C_PBuffer_270
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGroundF
d_isGroundF_416 ::
  T_PolyFunctor_236 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_416 v0
  = case coe v0 of
      C_PK_240 v1
        -> let v2 = d_isGround_420 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_242
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__244 v1 v2
        -> let v3 = d_isGroundF_416 (coe v1) in
           coe
             (let v4 = d_isGroundF_416 (coe v2) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                        -> case coe v4 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))
                             _ -> coe v5
                      _ -> coe v5)))
      C__P'8855'__246 v1 v2
        -> let v3 = d_isGroundF_416 (coe v1) in
           coe
             (let v4 = d_isGroundF_416 (coe v2) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                        -> case coe v4 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))
                             _ -> coe v5
                      _ -> coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_420 ::
  T_PolyType_238 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_420 v0
  = case coe v0 of
      C_PUnit_248
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_250
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__252 v1 v2
        -> let v3 = d_isGround_420 (coe v1) in
           coe
             (let v4 = d_isGround_420 (coe v2) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                        -> case coe v4 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))
                             _ -> coe v5
                      _ -> coe v5)))
      C__P'43'__254 v1 v2
        -> let v3 = d_isGround_420 (coe v1) in
           coe
             (let v4 = d_isGround_420 (coe v2) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                        -> case coe v4 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))
                             _ -> coe v5
                      _ -> coe v5)))
      C__P'8658''91'_'93'__256 v1 v2 v3
        -> let v4 = d_isGround_420 (coe v1) in
           coe
             (let v5 = d_isGround_420 (coe v3) in
              coe
                (let v6
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                        -> case coe v5 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                       (coe v8))
                             _ -> coe v6
                      _ -> coe v6)))
      C_PEff_258 v1 v2
        -> let v3 = d_isGround_420 (coe v1) in
           coe
             (let v4 = d_isGround_420 (coe v2) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                        -> case coe v4 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))
                             _ -> coe v5
                      _ -> coe v5)))
      C_Pμ'45'type_260 v1
        -> let v2 = d_isGroundF_416 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_262 v1
        -> let v2 = d_isGroundF_416 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_264
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_266
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PStr_268
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PBuffer_270
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_272 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_578 ::
  T_PolyType_238 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_578 v0
  = case coe v0 of
      C_PUnit_248 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_250 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__252 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_578 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_578 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__254 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_578 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_578 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__256 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_578 (coe v1))
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
                            (d_showPolyType_578 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_258 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_578 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_578 (coe v2))))
      C_Pμ'45'type_260 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_580 (coe v1))
      C_Pν'45'type_262 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_580 (coe v1))
      C_PInt_264 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_266 -> coe ("Float" :: Data.Text.Text)
      C_PStr_268 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_270 -> coe ("Buffer" :: Data.Text.Text)
      C_PTVar_272 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_580 ::
  T_PolyFunctor_236 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_580 v0
  = case coe v0 of
      C_PK_240 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_578 (coe v1)) (")" :: Data.Text.Text))
      C_PId_242 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__244 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_580 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_580 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__246 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_580 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_580 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_616 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_616 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_Zero_6
           -> case coe v1 of
                C_Zero_6 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_One_8
           -> case coe v1 of
                C_One_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Many_10
           -> case coe v1 of
                C_Many_10 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.purityEqBool
d_purityEqBool_618 :: T_Purity_32 -> T_Purity_32 -> Bool
d_purityEqBool_618 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_pure_34
           -> case coe v1 of
                C_pure_34 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_eff_36
           -> case coe v1 of
                C_eff_36 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.typeEqBool
d_typeEqBool_620 :: T_Type_108 -> T_Type_108 -> Bool
d_typeEqBool_620 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_Unit_118
           -> case coe v1 of
                C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Void_120
           -> case coe v1 of
                C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'42'__122 v3 v4
           -> case coe v1 of
                C__'42'__122 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_620 (coe v3) (coe v5))
                       (coe d_typeEqBool_620 (coe v4) (coe v6))
                _ -> coe v2
         C__'43'__124 v3 v4
           -> case coe v1 of
                C__'43'__124 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_620 (coe v3) (coe v5))
                       (coe d_typeEqBool_620 (coe v4) (coe v6))
                _ -> coe v2
         C__'8658''91'_'93'__126 v3 v4 v5
           -> case coe v4 of
                C_mk'45'kind_50 v6 v7
                  -> case coe v1 of
                       C__'8658''91'_'93'__126 v8 v9 v10
                         -> case coe v9 of
                              C_mk'45'kind_50 v11 v12
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_quantityEqBool_616 (coe v6) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_purityEqBool_618 (coe v7) (coe v12))
                                        (coe
                                           MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                           (coe d_typeEqBool_620 (coe v3) (coe v8))
                                           (coe d_typeEqBool_620 (coe v5) (coe v10))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         C_μ'45'type_128 v3
           -> case coe v1 of
                C_μ'45'type_128 v4 -> coe d_functorEqBool_622 (coe v3) (coe v4)
                _ -> coe v2
         C_ν'45'type_130 v3
           -> case coe v1 of
                C_ν'45'type_130 v4 -> coe d_functorEqBool_622 (coe v3) (coe v4)
                _ -> coe v2
         C_Int_132
           -> case coe v1 of
                C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Float_134
           -> case coe v1 of
                C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Str_136
           -> case coe v1 of
                C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Buffer_138
           -> case coe v1 of
                C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.functorEqBool
d_functorEqBool_622 :: T_Functor_106 -> T_Functor_106 -> Bool
d_functorEqBool_622 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_K_110 v3
           -> case coe v1 of
                C_K_110 v4 -> coe d_typeEqBool_620 (coe v3) (coe v4)
                _ -> coe v2
         C_Id_112
           -> case coe v1 of
                C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8853'__114 v3 v4
           -> case coe v1 of
                C__'8853'__114 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_622 (coe v3) (coe v5))
                       (coe d_functorEqBool_622 (coe v4) (coe v6))
                _ -> coe v2
         C__'8855'__116 v3 v4
           -> case coe v1 of
                C__'8855'__116 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_622 (coe v3) (coe v5))
                       (coe d_functorEqBool_622 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Subst
d_Subst_684 :: ()
d_Subst_684 = erased
-- Once.Type._._×'_
d__'215'''__690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'''__690 = erased
-- Once.Type.lookupSubst
d_lookupSubst_692 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_Type_108
d_lookupSubst_692 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_692 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extendSubst
d_extendSubst_726 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_726 v0 v1 v2
  = let v3 = d_lookupSubst_692 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_typeEqBool_620 (coe v1) (coe v4))
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
-- Once.Type.instantiate
d_instantiate_756 ::
  T_PolyType_238 ->
  T_Type_108 -> Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_756 v0 v1
  = coe
      d_instantiateAcc_758 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.instantiateAcc
d_instantiateAcc_758 ::
  T_PolyType_238 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_758 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PUnit_248
           -> case coe v1 of
                C_Unit_118
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PVoid_250
           -> case coe v1 of
                C_Void_120
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'42'__252 v4 v5
           -> case coe v1 of
                C__'42'__122 v6 v7
                  -> let v8 = d_instantiateAcc_758 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_758 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'43'__254 v4 v5
           -> case coe v1 of
                C__'43'__124 v6 v7
                  -> let v8 = d_instantiateAcc_758 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_758 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8658''91'_'93'__256 v4 v5 v6
           -> case coe v1 of
                C__'8658''91'_'93'__126 v7 v8 v9
                  -> case coe v8 of
                       C_mk'45'kind_50 v10 v11
                         -> case coe v11 of
                              C_pure_34
                                -> let v12 = d_quantityEqBool_616 (coe v5) (coe v10) in
                                   coe
                                     (if coe v12
                                        then let v13
                                                   = d_instantiateAcc_758
                                                       (coe v4) (coe v7) (coe v2) in
                                             coe
                                               (case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                    -> coe
                                                         d_instantiateAcc_758 (coe v6) (coe v9)
                                                         (coe v14)
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v13
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         C_PEff_258 v4 v5
           -> case coe v1 of
                C__'8658''91'_'93'__126 v6 v7 v8
                  -> case coe v7 of
                       C_mk'45'kind_50 v9 v10
                         -> case coe v10 of
                              C_eff_36
                                -> let v11 = d_instantiateAcc_758 (coe v4) (coe v6) (coe v2) in
                                   coe
                                     (case coe v11 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                          -> coe d_instantiateAcc_758 (coe v5) (coe v8) (coe v12)
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         C_Pμ'45'type_260 v4
           -> case coe v1 of
                C_μ'45'type_128 v5
                  -> coe d_instantiateFunctor_760 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_Pν'45'type_262 v4
           -> case coe v1 of
                C_ν'45'type_130 v5
                  -> coe d_instantiateFunctor_760 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PInt_264
           -> case coe v1 of
                C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PFloat_266
           -> case coe v1 of
                C_Float_134
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PStr_268
           -> case coe v1 of
                C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PBuffer_270
           -> case coe v1 of
                C_Buffer_138
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PTVar_272 v4 -> coe d_extendSubst_726 (coe v4) (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.instantiateFunctor
d_instantiateFunctor_760 ::
  T_PolyFunctor_236 ->
  T_Functor_106 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_760 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PK_240 v4
           -> case coe v1 of
                C_K_110 v5 -> coe d_instantiateAcc_758 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PId_242
           -> case coe v1 of
                C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'8853'__244 v4 v5
           -> case coe v1 of
                C__'8853'__114 v6 v7
                  -> let v8 = d_instantiateFunctor_760 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_760 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8855'__246 v4 v5
           -> case coe v1 of
                C__'8855'__116 v6 v7
                  -> let v8 = d_instantiateFunctor_760 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_760 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.applySubst
d_applySubst_1064 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyType_238 -> Maybe T_Type_108
d_applySubst_1064 v0 v1
  = case coe v1 of
      C_PUnit_248
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_118)
      C_PVoid_250
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_120)
      C__P'42'__252 v2 v3
        -> let v4 = d_applySubst_1064 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1064 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'42'__122 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'43'__254 v2 v3
        -> let v4 = d_applySubst_1064 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1064 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'43'__124 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8658''91'_'93'__256 v2 v3 v4
        -> let v5 = d_applySubst_1064 (coe v0) (coe v2) in
           coe
             (let v6 = d_applySubst_1064 (coe v0) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C__'8658''91'_'93'__126 (coe v7)
                                    (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34)) (coe v8))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_PEff_258 v2 v3
        -> let v4 = d_applySubst_1064 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1064 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C__'8658''91'_'93'__126 (coe v6)
                                    (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36)) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_Pμ'45'type_260 v2
        -> let v3 = d_applySubstFunctor_1066 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_μ'45'type_128 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_262 v2
        -> let v3 = d_applySubstFunctor_1066 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_ν'45'type_130 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_264
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_132)
      C_PFloat_266
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_134)
      C_PStr_268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_136)
      C_PBuffer_270
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_138)
      C_PTVar_272 v2 -> coe d_lookupSubst_692 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubstFunctor
d_applySubstFunctor_1066 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyFunctor_236 -> Maybe T_Functor_106
d_applySubstFunctor_1066 v0 v1
  = case coe v1 of
      C_PK_240 v2
        -> let v3 = d_applySubst_1064 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_110 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_242
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_112)
      C__P'8853'__244 v2 v3
        -> let v4 = d_applySubstFunctor_1066 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1066 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8853'__114 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8855'__246 v2 v3
        -> let v4 = d_applySubstFunctor_1066 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1066 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8855'__116 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.schemaArrowCodomain
d_schemaArrowCodomain_1288 ::
  T_PolyType_238 -> T_Type_108 -> Maybe T_Type_108
d_schemaArrowCodomain_1288 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C__P'8658''91'_'93'__256 v3 v4 v5
           -> let v6
                    = d_instantiateAcc_758
                        (coe v3) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> coe d_applySubst_1064 (coe v7) (coe v5)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
