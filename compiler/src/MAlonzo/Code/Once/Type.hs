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
-- Once.Type.FitsInReg
d_FitsInReg_188 a0 = ()
data T_FitsInReg_188 = C_fits'45'int_190 | C_fits'45'float_192
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_196 :: T_Type_108 -> Maybe T_FitsInReg_188
d_fits'45'in'45'reg'63'_196 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_Int_132
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_190)
         C_Float_134
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_192)
         _ -> coe v1)
-- Once.Type.showType
d_showType_198 ::
  T_Type_108 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_198 v0
  = case coe v0 of
      C_Unit_118 -> coe ("Unit" :: Data.Text.Text)
      C_Void_120 -> coe ("Void" :: Data.Text.Text)
      C__'42'__122 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_198 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_198 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__124 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_198 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_198 (coe v2)) (")" :: Data.Text.Text))))
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
                              (d_showType_198 (coe v1))
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
                                          (d_showType_198 (coe v3)) (")" :: Data.Text.Text))))))
                    C_eff_36
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_198 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_198 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_200 (coe v1))
      C_ν'45'type_130 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_200 (coe v1))
      C_Int_132 -> coe ("Int" :: Data.Text.Text)
      C_Float_134 -> coe ("Float" :: Data.Text.Text)
      C_Str_136 -> coe ("String" :: Data.Text.Text)
      C_Buffer_138 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_200 ::
  T_Functor_106 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_200 v0
  = case coe v0 of
      C_K_110 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_198 (coe v1)) (")" :: Data.Text.Text))
      C_Id_112 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__114 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_200 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_200 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_200 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_200 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.PolyFunctor
d_PolyFunctor_234 = ()
data T_PolyFunctor_234
  = C_PK_238 T_PolyType_236 | C_PId_240 |
    C__P'8853'__242 T_PolyFunctor_234 T_PolyFunctor_234 |
    C__P'8855'__244 T_PolyFunctor_234 T_PolyFunctor_234
-- Once.Type.PolyType
d_PolyType_236 = ()
data T_PolyType_236
  = C_PUnit_246 | C_PVoid_248 |
    C__P'42'__250 T_PolyType_236 T_PolyType_236 |
    C__P'43'__252 T_PolyType_236 T_PolyType_236 |
    C__P'8658''91'_'93'__254 T_PolyType_236 T_Quantity_4
                             T_PolyType_236 |
    C_PEff_256 T_PolyType_236 T_PolyType_236 |
    C_Pμ'45'type_258 T_PolyFunctor_234 |
    C_Pν'45'type_260 T_PolyFunctor_234 | C_PInt_262 | C_PFloat_264 |
    C_PStr_266 | C_PBuffer_268 |
    C_PTVar_270 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_272 :: T_PolyFunctor_234 -> ()
d_GroundF_272 = erased
-- Once.Type.Ground
d_Ground_274 :: T_PolyType_236 -> ()
d_Ground_274 = erased
-- Once.Type.extractGroundF
d_extractGroundF_308 ::
  T_PolyFunctor_234 -> AgdaAny -> T_Functor_106
d_extractGroundF_308 v0 v1
  = case coe v0 of
      C_PK_238 v2
        -> coe C_K_110 (coe d_extractGround_312 (coe v2) (coe v1))
      C_PId_240 -> coe C_Id_112
      C__P'8853'__242 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__114 (coe d_extractGroundF_308 (coe v2) (coe v4))
                    (coe d_extractGroundF_308 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__244 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__116 (coe d_extractGroundF_308 (coe v2) (coe v4))
                    (coe d_extractGroundF_308 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_312 :: T_PolyType_236 -> AgdaAny -> T_Type_108
d_extractGround_312 v0 v1
  = case coe v0 of
      C_PUnit_246 -> coe C_Unit_118
      C_PVoid_248 -> coe C_Void_120
      C__P'42'__250 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__122 (coe d_extractGround_312 (coe v2) (coe v4))
                    (coe d_extractGround_312 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__252 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__124 (coe d_extractGround_312 (coe v2) (coe v4))
                    (coe d_extractGround_312 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__254 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_312 (coe v2) (coe v5))
                    (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))
                    (coe d_extractGround_312 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_256 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8658''91'_'93'__126 (coe d_extractGround_312 (coe v2) (coe v4))
                    (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))
                    (coe d_extractGround_312 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_258 v2
        -> coe C_μ'45'type_128 (coe d_extractGroundF_308 (coe v2) (coe v1))
      C_Pν'45'type_260 v2
        -> coe C_ν'45'type_130 (coe d_extractGroundF_308 (coe v2) (coe v1))
      C_PInt_262 -> coe C_Int_132
      C_PFloat_264 -> coe C_Float_134
      C_PStr_266 -> coe C_Str_136
      C_PBuffer_268 -> coe C_Buffer_138
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embedFunctor
d_embedFunctor_376 :: T_Functor_106 -> T_PolyFunctor_234
d_embedFunctor_376 v0
  = case coe v0 of
      C_K_110 v1 -> coe C_PK_238 (coe d_embed_378 (coe v1))
      C_Id_112 -> coe C_PId_240
      C__'8853'__114 v1 v2
        -> coe
             C__P'8853'__242 (coe d_embedFunctor_376 (coe v1))
             (coe d_embedFunctor_376 (coe v2))
      C__'8855'__116 v1 v2
        -> coe
             C__P'8855'__244 (coe d_embedFunctor_376 (coe v1))
             (coe d_embedFunctor_376 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_378 :: T_Type_108 -> T_PolyType_236
d_embed_378 v0
  = case coe v0 of
      C_Unit_118 -> coe C_PUnit_246
      C_Void_120 -> coe C_PVoid_248
      C__'42'__122 v1 v2
        -> coe
             C__P'42'__250 (coe d_embed_378 (coe v1)) (coe d_embed_378 (coe v2))
      C__'43'__124 v1 v2
        -> coe
             C__P'43'__252 (coe d_embed_378 (coe v1)) (coe d_embed_378 (coe v2))
      C__'8658''91'_'93'__126 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    C_pure_34
                      -> coe
                           C__P'8658''91'_'93'__254 (coe d_embed_378 (coe v1)) (coe v4)
                           (coe d_embed_378 (coe v3))
                    C_eff_36
                      -> coe
                           C_PEff_256 (coe d_embed_378 (coe v1)) (coe d_embed_378 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_128 v1
        -> coe C_Pμ'45'type_258 (coe d_embedFunctor_376 (coe v1))
      C_ν'45'type_130 v1
        -> coe C_Pν'45'type_260 (coe d_embedFunctor_376 (coe v1))
      C_Int_132 -> coe C_PInt_262
      C_Float_134 -> coe C_PFloat_264
      C_Str_136 -> coe C_PStr_266
      C_Buffer_138 -> coe C_PBuffer_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_416 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_416 ~v0 ~v1 v2 v3 = du_both'45'ground_416 v2 v3
du_both'45'ground_416 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_416 v0 v1
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
d_isGroundF_424 ::
  T_PolyFunctor_234 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_424 v0
  = case coe v0 of
      C_PK_238 v1 -> coe d_isGround_428 (coe v1)
      C_PId_240
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__242 v1 v2
        -> coe
             du_both'45'ground_416 (coe d_isGroundF_424 (coe v1))
             (coe d_isGroundF_424 (coe v2))
      C__P'8855'__244 v1 v2
        -> coe
             du_both'45'ground_416 (coe d_isGroundF_424 (coe v1))
             (coe d_isGroundF_424 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_428 ::
  T_PolyType_236 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_428 v0
  = case coe v0 of
      C_PUnit_246
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_248
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__250 v1 v2
        -> coe
             du_both'45'ground_416 (coe d_isGround_428 (coe v1))
             (coe d_isGround_428 (coe v2))
      C__P'43'__252 v1 v2
        -> coe
             du_both'45'ground_416 (coe d_isGround_428 (coe v1))
             (coe d_isGround_428 (coe v2))
      C__P'8658''91'_'93'__254 v1 v2 v3
        -> coe
             du_both'45'ground_416 (coe d_isGround_428 (coe v1))
             (coe d_isGround_428 (coe v3))
      C_PEff_256 v1 v2
        -> coe
             du_both'45'ground_416 (coe d_isGround_428 (coe v1))
             (coe d_isGround_428 (coe v2))
      C_Pμ'45'type_258 v1 -> coe d_isGroundF_424 (coe v1)
      C_Pν'45'type_260 v1 -> coe d_isGroundF_424 (coe v1)
      C_PInt_262
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_264
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PStr_266
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PBuffer_268
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_270 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_460 ::
  T_PolyType_236 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_460 v0
  = case coe v0 of
      C_PUnit_246 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_248 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__250 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_460 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_460 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__252 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_460 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_460 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__254 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_460 (coe v1))
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
                            (d_showPolyType_460 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_256 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_460 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_460 (coe v2))))
      C_Pμ'45'type_258 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_462 (coe v1))
      C_Pν'45'type_260 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_462 (coe v1))
      C_PInt_262 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_264 -> coe ("Float" :: Data.Text.Text)
      C_PStr_266 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_268 -> coe ("Buffer" :: Data.Text.Text)
      C_PTVar_270 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_462 ::
  T_PolyFunctor_234 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_462 v0
  = case coe v0 of
      C_PK_238 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_460 (coe v1)) (")" :: Data.Text.Text))
      C_PId_240 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__242 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_462 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_462 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__244 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_462 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_462 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_498 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_498 v0 v1
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
d_purityEqBool_500 :: T_Purity_32 -> T_Purity_32 -> Bool
d_purityEqBool_500 v0 v1
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
d_typeEqBool_502 :: T_Type_108 -> T_Type_108 -> Bool
d_typeEqBool_502 v0 v1
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
                    (coe d_typeEqBool_502 (coe v2) (coe v4))
                    (coe d_typeEqBool_502 (coe v3) (coe v5))
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
                    (coe d_typeEqBool_502 (coe v2) (coe v4))
                    (coe d_typeEqBool_502 (coe v3) (coe v5))
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
                                  (coe d_quantityEqBool_498 (coe v8) (coe v10))
                                  (coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_purityEqBool_500 (coe v9) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_typeEqBool_502 (coe v2) (coe v5))
                                        (coe d_typeEqBool_502 (coe v4) (coe v7))))
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
             C_μ'45'type_128 v3 -> coe d_functorEqBool_504 (coe v2) (coe v3)
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
             C_ν'45'type_130 v3 -> coe d_functorEqBool_504 (coe v2) (coe v3)
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
d_functorEqBool_504 :: T_Functor_106 -> T_Functor_106 -> Bool
d_functorEqBool_504 v0 v1
  = case coe v0 of
      C_K_110 v2
        -> case coe v1 of
             C_K_110 v3 -> coe d_typeEqBool_502 (coe v2) (coe v3)
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
                    (coe d_functorEqBool_504 (coe v2) (coe v4))
                    (coe d_functorEqBool_504 (coe v3) (coe v5))
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
                    (coe d_functorEqBool_504 (coe v2) (coe v4))
                    (coe d_functorEqBool_504 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Subst
d_Subst_566 :: ()
d_Subst_566 = erased
-- Once.Type._._×'_
d__'215'''__572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'''__572 = erased
-- Once.Type.lookupSubst
d_lookupSubst_574 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_Type_108
d_lookupSubst_574 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_574 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extendSubst
d_extendSubst_608 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_608 v0 v1 v2
  = let v3 = d_lookupSubst_574 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_typeEqBool_502 (coe v1) (coe v4))
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
d_maybe'45'bind_642 ::
  () ->
  () -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'bind_642 ~v0 ~v1 v2 v3 = du_maybe'45'bind_642 v2 v3
du_maybe'45'bind_642 ::
  (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'bind_642 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.maybe-pair
d_maybe'45'pair_654 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'pair_654 ~v0 ~v1 ~v2 v3 v4 v5
  = du_maybe'45'pair_654 v3 v4 v5
du_maybe'45'pair_654 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'pair_654 v0 v1 v2
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
d_if'45'true'45'maybe_664 ::
  () -> Bool -> Maybe AgdaAny -> Maybe AgdaAny
d_if'45'true'45'maybe_664 ~v0 v1 v2
  = du_if'45'true'45'maybe_664 v1 v2
du_if'45'true'45'maybe_664 ::
  Bool -> Maybe AgdaAny -> Maybe AgdaAny
du_if'45'true'45'maybe_664 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Type.instantiate
d_instantiate_668 ::
  T_PolyType_236 ->
  T_Type_108 -> Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_668 v0 v1
  = coe
      d_instantiateAcc_670 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.instantiateAcc
d_instantiateAcc_670 ::
  T_PolyType_236 ->
  T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_670 v0 v1 v2
  = case coe v0 of
      C_PUnit_246
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
      C_PVoid_248
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
      C__P'42'__250 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v5 v6
               -> coe
                    du_maybe'45'bind_642 (coe d_instantiateAcc_670 (coe v4) (coe v6))
                    (coe d_instantiateAcc_670 (coe v3) (coe v5) (coe v2))
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
      C__P'43'__252 v3 v4
        -> case coe v1 of
             C_Unit_118 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Void_120 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'42'__122 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'43'__124 v5 v6
               -> coe
                    du_maybe'45'bind_642 (coe d_instantiateAcc_670 (coe v4) (coe v6))
                    (coe d_instantiateAcc_670 (coe v3) (coe v5) (coe v2))
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
      C__P'8658''91'_'93'__254 v3 v4 v5
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
                                  du_if'45'true'45'maybe_664
                                  (coe d_quantityEqBool_498 (coe v4) (coe v9))
                                  (coe
                                     du_maybe'45'bind_642
                                     (coe d_instantiateAcc_670 (coe v5) (coe v8))
                                     (coe d_instantiateAcc_670 (coe v3) (coe v6) (coe v2)))
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
      C_PEff_256 v3 v4
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
                                  du_maybe'45'bind_642 (coe d_instantiateAcc_670 (coe v4) (coe v7))
                                  (coe d_instantiateAcc_670 (coe v3) (coe v5) (coe v2))
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
      C_Pμ'45'type_258 v3
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
               -> coe d_instantiateFunctor_672 (coe v3) (coe v4) (coe v2)
             C_ν'45'type_130 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pν'45'type_260 v3
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
               -> coe d_instantiateFunctor_672 (coe v3) (coe v4) (coe v2)
             C_Int_132 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Float_134 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Str_136 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Buffer_138 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PInt_262
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
      C_PFloat_264
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
      C_PStr_266
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
      C_PBuffer_268
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
      C_PTVar_270 v3 -> coe d_extendSubst_608 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.instantiateFunctor
d_instantiateFunctor_672 ::
  T_PolyFunctor_234 ->
  T_Functor_106 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_672 v0 v1 v2
  = case coe v0 of
      C_PK_238 v3
        -> case coe v1 of
             C_K_110 v4 -> coe d_instantiateAcc_670 (coe v3) (coe v4) (coe v2)
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PId_240
        -> case coe v1 of
             C_K_110 v3 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             C__'8853'__114 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8853'__242 v3 v4
        -> case coe v1 of
             C_K_110 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v5 v6
               -> coe
                    du_maybe'45'bind_642
                    (coe d_instantiateFunctor_672 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_672 (coe v3) (coe v5) (coe v2))
             C__'8855'__116 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__244 v3 v4
        -> case coe v1 of
             C_K_110 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_Id_112 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8853'__114 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C__'8855'__116 v5 v6
               -> coe
                    du_maybe'45'bind_642
                    (coe d_instantiateFunctor_672 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_672 (coe v3) (coe v5) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubst
d_applySubst_780 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyType_236 -> Maybe T_Type_108
d_applySubst_780 v0 v1
  = case coe v1 of
      C_PUnit_246
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_118)
      C_PVoid_248
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_120)
      C__P'42'__250 v2 v3
        -> coe
             du_maybe'45'pair_654 (coe C__'42'__122)
             (coe d_applySubst_780 (coe v0) (coe v2))
             (coe d_applySubst_780 (coe v0) (coe v3))
      C__P'43'__252 v2 v3
        -> coe
             du_maybe'45'pair_654 (coe C__'43'__124)
             (coe d_applySubst_780 (coe v0) (coe v2))
             (coe d_applySubst_780 (coe v0) (coe v3))
      C__P'8658''91'_'93'__254 v2 v3 v4
        -> coe
             du_maybe'45'pair_654
             (coe
                (\ v5 ->
                   coe
                     C__'8658''91'_'93'__126 (coe v5)
                     (coe C_mk'45'kind_50 (coe v3) (coe C_pure_34))))
             (coe d_applySubst_780 (coe v0) (coe v2))
             (coe d_applySubst_780 (coe v0) (coe v4))
      C_PEff_256 v2 v3
        -> coe
             du_maybe'45'pair_654
             (coe
                (\ v4 ->
                   coe
                     C__'8658''91'_'93'__126 (coe v4)
                     (coe C_mk'45'kind_50 (coe C_Many_10) (coe C_eff_36))))
             (coe d_applySubst_780 (coe v0) (coe v2))
             (coe d_applySubst_780 (coe v0) (coe v3))
      C_Pμ'45'type_258 v2
        -> coe
             du_maybe'45'bind_642
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe C_μ'45'type_128 (coe v3))))
             (coe d_applySubstFunctor_782 (coe v0) (coe v2))
      C_Pν'45'type_260 v2
        -> coe
             du_maybe'45'bind_642
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe C_ν'45'type_130 (coe v3))))
             (coe d_applySubstFunctor_782 (coe v0) (coe v2))
      C_PInt_262
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_132)
      C_PFloat_264
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_134)
      C_PStr_266
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_136)
      C_PBuffer_268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_138)
      C_PTVar_270 v2 -> coe d_lookupSubst_574 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubstFunctor
d_applySubstFunctor_782 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyFunctor_234 -> Maybe T_Functor_106
d_applySubstFunctor_782 v0 v1
  = case coe v1 of
      C_PK_238 v2
        -> coe
             du_maybe'45'bind_642
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_110 (coe v3))))
             (coe d_applySubst_780 (coe v0) (coe v2))
      C_PId_240
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_112)
      C__P'8853'__242 v2 v3
        -> coe
             du_maybe'45'pair_654 (coe C__'8853'__114)
             (coe d_applySubstFunctor_782 (coe v0) (coe v2))
             (coe d_applySubstFunctor_782 (coe v0) (coe v3))
      C__P'8855'__244 v2 v3
        -> coe
             du_maybe'45'pair_654 (coe C__'8855'__116)
             (coe d_applySubstFunctor_782 (coe v0) (coe v2))
             (coe d_applySubstFunctor_782 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.schemaArrowCodomain
d_schemaArrowCodomain_852 ::
  T_PolyType_236 -> T_Type_108 -> Maybe T_Type_108
d_schemaArrowCodomain_852 v0 v1
  = case coe v0 of
      C_PUnit_246 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PVoid_248 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'42'__250 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'43'__252 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C__P'8658''91'_'93'__254 v2 v3 v4
        -> coe
             du_maybe'45'bind_642
             (coe (\ v5 -> d_applySubst_780 (coe v5) (coe v4)))
             (coe d_instantiate_668 (coe v2) (coe v1))
      C_PEff_256 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_Pμ'45'type_258 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_Pν'45'type_260 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PInt_262 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PFloat_264 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PStr_266 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PBuffer_268 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_PTVar_270 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
