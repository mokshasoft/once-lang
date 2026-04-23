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
-- Once.Type._⊔q_
d__'8852'q__28 :: T_Quantity_4 -> T_Quantity_4 -> T_Quantity_4
d__'8852'q__28 v0 v1
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
d__'8804'q__32 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d__'8804'q__32 v0 v1
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
d_showQuantity_34 ::
  T_Quantity_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_34 v0
  = case coe v0 of
      C_Zero_6 -> coe ("0" :: Data.Text.Text)
      C_One_8 -> coe ("1" :: Data.Text.Text)
      C_Many_10 -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Purity
d_Purity_36 = ()
data T_Purity_36 = C_pure_38 | C_eff_40
-- Once.Type.showPurity
d_showPurity_42 ::
  T_Purity_36 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPurity_42 v0
  = case coe v0 of
      C_pure_38 -> coe ("pure" :: Data.Text.Text)
      C_eff_40 -> coe ("eff" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ArrowKind
d_ArrowKind_44 = ()
data T_ArrowKind_44 = C_mk'45'kind_54 T_Quantity_4 T_Purity_36
-- Once.Type.ArrowKind.quantity
d_quantity_50 :: T_ArrowKind_44 -> T_Quantity_4
d_quantity_50 v0
  = case coe v0 of
      C_mk'45'kind_54 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.ArrowKind.purity
d_purity_52 :: T_ArrowKind_44 -> T_Purity_36
d_purity_52 v0
  = case coe v0 of
      C_mk'45'kind_54 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showArrowKind
d_showArrowKind_56 ::
  T_ArrowKind_44 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArrowKind_56 v0
  = case coe v0 of
      C_mk'45'kind_54 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showQuantity_34 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("," :: Data.Text.Text) (d_showPurity_42 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.pureK
d_pureK_62 :: T_Quantity_4 -> T_ArrowKind_44
d_pureK_62 v0 = coe C_mk'45'kind_54 (coe v0) (coe C_pure_38)
-- Once.Type.effK
d_effK_66 :: T_ArrowKind_44
d_effK_66 = coe C_mk'45'kind_54 (coe C_Many_10) (coe C_eff_40)
-- Once.Type._≟p_
d__'8799'p__72 ::
  T_Purity_36 ->
  T_Purity_36 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'p__72 v0 v1
  = case coe v0 of
      C_pure_38
        -> case coe v1 of
             C_pure_38
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_eff_40
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_eff_40
        -> case coe v1 of
             C_pure_38
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_eff_40
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≟k_
d__'8799'k__78 ::
  T_ArrowKind_44 ->
  T_ArrowKind_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'k__78 v0 v1
  = case coe v0 of
      C_mk'45'kind_54 v2 v3
        -> case coe v1 of
             C_mk'45'kind_54 v4 v5
               -> let v6 = d__'8799'q__26 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'p__72 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Functor
d_Functor_124 = ()
data T_Functor_124
  = C_K_128 T_Type_126 | C_Id_130 |
    C__'8853'__132 T_Functor_124 T_Functor_124 |
    C__'8855'__134 T_Functor_124 T_Functor_124
-- Once.Type.Type
d_Type_126 = ()
data T_Type_126
  = C_Unit_136 | C_Void_138 | C__'42'__140 T_Type_126 T_Type_126 |
    C__'43'__142 T_Type_126 T_Type_126 |
    C__'8658''91'_'93'__144 T_Type_126 T_ArrowKind_44 T_Type_126 |
    C_μ'45'type_146 T_Functor_124 | C_ν'45'type_148 T_Functor_124 |
    C_Int_150 | C_Float_152 | C_Str_154 | C_Buffer_156
-- Once.Type._⊸_
d__'8888'__158 :: T_Type_126 -> T_Type_126 -> T_Type_126
d__'8888'__158 v0 v1
  = coe
      C__'8658''91'_'93'__144 (coe v0)
      (coe C_mk'45'kind_54 (coe C_One_8) (coe C_pure_38)) (coe v1)
-- Once.Type._⇒_
d__'8658'__164 :: T_Type_126 -> T_Type_126 -> T_Type_126
d__'8658'__164 v0 v1
  = coe
      C__'8658''91'_'93'__144 (coe v0)
      (coe C_mk'45'kind_54 (coe C_Many_10) (coe C_pure_38)) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__170 :: T_Type_126 -> T_Type_126 -> T_Type_126
d__'8658''8320'__170 v0 v1
  = coe
      C__'8658''91'_'93'__144 (coe v0)
      (coe C_mk'45'kind_54 (coe C_Zero_6) (coe C_pure_38)) (coe v1)
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_176 :: T_Functor_124 -> T_Type_126 -> T_Type_126
d_'10214'_'10215'T_176 v0 v1
  = case coe v0 of
      C_K_128 v2 -> coe v2
      C_Id_130 -> coe v1
      C__'8853'__132 v2 v3
        -> coe
             C__'43'__142 (coe d_'10214'_'10215'T_176 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_176 (coe v3) (coe v1))
      C__'8855'__134 v2 v3
        -> coe
             C__'42'__140 (coe d_'10214'_'10215'T_176 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_176 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_196 :: T_Functor_124
d_NatF_196
  = coe C__'8853'__132 (coe C_K_128 (coe C_Unit_136)) (coe C_Id_130)
-- Once.Type.ListF
d_ListF_198 :: T_Type_126 -> T_Functor_124
d_ListF_198 v0
  = coe
      C__'8853'__132 (coe C_K_128 (coe C_Unit_136))
      (coe C__'8855'__134 (coe C_K_128 (coe v0)) (coe C_Id_130))
-- Once.Type.TreeF
d_TreeF_202 :: T_Type_126 -> T_Functor_124
d_TreeF_202 v0
  = coe
      C__'8853'__132 (coe C_K_128 (coe v0))
      (coe C__'8855'__134 (coe C_Id_130) (coe C_Id_130))
-- Once.Type.IsPrimitive
d_IsPrimitive_206 a0 = ()
data T_IsPrimitive_206
  = C_is'45'unit_208 | C_is'45'int_210 | C_is'45'float_212 |
    C_is'45'str_214 | C_is'45'buffer_216
-- Once.Type.showType
d_showType_218 ::
  T_Type_126 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_218 v0
  = case coe v0 of
      C_Unit_136 -> coe ("Unit" :: Data.Text.Text)
      C_Void_138 -> coe ("Void" :: Data.Text.Text)
      C__'42'__140 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_218 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_218 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__142 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_218 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_218 (coe v2)) (")" :: Data.Text.Text))))
      C__'8658''91'_'93'__144 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_54 v4 v5
               -> case coe v5 of
                    C_pure_38
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_218 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_showQuantity_34 (coe v4))
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("\8594 " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (d_showType_218 (coe v3)) (")" :: Data.Text.Text))))))
                    C_eff_40
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_218 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_218 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_146 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_220 (coe v1))
      C_ν'45'type_148 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_220 (coe v1))
      C_Int_150 -> coe ("Int" :: Data.Text.Text)
      C_Float_152 -> coe ("Float" :: Data.Text.Text)
      C_Str_154 -> coe ("String" :: Data.Text.Text)
      C_Buffer_156 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_220 ::
  T_Functor_124 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_220 v0
  = case coe v0 of
      C_K_128 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_218 (coe v1)) (")" :: Data.Text.Text))
      C_Id_130 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__132 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_220 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_220 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__134 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_220 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_220 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.PolyFunctor
d_PolyFunctor_254 = ()
data T_PolyFunctor_254
  = C_PK_258 T_PolyType_256 | C_PId_260 |
    C__P'8853'__262 T_PolyFunctor_254 T_PolyFunctor_254 |
    C__P'8855'__264 T_PolyFunctor_254 T_PolyFunctor_254
-- Once.Type.PolyType
d_PolyType_256 = ()
data T_PolyType_256
  = C_PUnit_266 | C_PVoid_268 |
    C__P'42'__270 T_PolyType_256 T_PolyType_256 |
    C__P'43'__272 T_PolyType_256 T_PolyType_256 |
    C__P'8658''91'_'93'__274 T_PolyType_256 T_Quantity_4
                             T_PolyType_256 |
    C_PEff_276 T_PolyType_256 T_PolyType_256 |
    C_Pμ'45'type_278 T_PolyFunctor_254 |
    C_Pν'45'type_280 T_PolyFunctor_254 | C_PInt_282 | C_PFloat_284 |
    C_PStr_286 | C_PBuffer_288 |
    C_PTVar_290 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_292 :: T_PolyFunctor_254 -> ()
d_GroundF_292 = erased
-- Once.Type.Ground
d_Ground_294 :: T_PolyType_256 -> ()
d_Ground_294 = erased
-- Once.Type.extractGroundF
d_extractGroundF_328 ::
  T_PolyFunctor_254 -> AgdaAny -> T_Functor_124
d_extractGroundF_328 v0 v1
  = case coe v0 of
      C_PK_258 v2
        -> coe C_K_128 (coe d_extractGround_332 (coe v2) (coe v1))
      C_PId_260 -> coe C_Id_130
      C__P'8853'__262 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__132 (coe d_extractGroundF_328 (coe v2) (coe v4))
                    (coe d_extractGroundF_328 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__264 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__134 (coe d_extractGroundF_328 (coe v2) (coe v4))
                    (coe d_extractGroundF_328 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_332 :: T_PolyType_256 -> AgdaAny -> T_Type_126
d_extractGround_332 v0 v1
  = case coe v0 of
      C_PUnit_266 -> coe C_Unit_136
      C_PVoid_268 -> coe C_Void_138
      C__P'42'__270 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__140 (coe d_extractGround_332 (coe v2) (coe v4))
                    (coe d_extractGround_332 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__272 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__142 (coe d_extractGround_332 (coe v2) (coe v4))
                    (coe d_extractGround_332 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__274 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__144 (coe d_extractGround_332 (coe v2) (coe v5))
                    (coe C_mk'45'kind_54 (coe v3) (coe C_pure_38))
                    (coe d_extractGround_332 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_276 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8658''91'_'93'__144 (coe d_extractGround_332 (coe v2) (coe v4))
                    (coe C_mk'45'kind_54 (coe C_Many_10) (coe C_eff_40))
                    (coe d_extractGround_332 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_278 v2
        -> coe C_μ'45'type_146 (coe d_extractGroundF_328 (coe v2) (coe v1))
      C_Pν'45'type_280 v2
        -> coe C_ν'45'type_148 (coe d_extractGroundF_328 (coe v2) (coe v1))
      C_PInt_282 -> coe C_Int_150
      C_PFloat_284 -> coe C_Float_152
      C_PStr_286 -> coe C_Str_154
      C_PBuffer_288 -> coe C_Buffer_156
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embedFunctor
d_embedFunctor_396 :: T_Functor_124 -> T_PolyFunctor_254
d_embedFunctor_396 v0
  = case coe v0 of
      C_K_128 v1 -> coe C_PK_258 (coe d_embed_398 (coe v1))
      C_Id_130 -> coe C_PId_260
      C__'8853'__132 v1 v2
        -> coe
             C__P'8853'__262 (coe d_embedFunctor_396 (coe v1))
             (coe d_embedFunctor_396 (coe v2))
      C__'8855'__134 v1 v2
        -> coe
             C__P'8855'__264 (coe d_embedFunctor_396 (coe v1))
             (coe d_embedFunctor_396 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_398 :: T_Type_126 -> T_PolyType_256
d_embed_398 v0
  = case coe v0 of
      C_Unit_136 -> coe C_PUnit_266
      C_Void_138 -> coe C_PVoid_268
      C__'42'__140 v1 v2
        -> coe
             C__P'42'__270 (coe d_embed_398 (coe v1)) (coe d_embed_398 (coe v2))
      C__'43'__142 v1 v2
        -> coe
             C__P'43'__272 (coe d_embed_398 (coe v1)) (coe d_embed_398 (coe v2))
      C__'8658''91'_'93'__144 v1 v2 v3
        -> case coe v2 of
             C_mk'45'kind_54 v4 v5
               -> case coe v5 of
                    C_pure_38
                      -> coe
                           C__P'8658''91'_'93'__274 (coe d_embed_398 (coe v1)) (coe v4)
                           (coe d_embed_398 (coe v3))
                    C_eff_40
                      -> coe
                           C_PEff_276 (coe d_embed_398 (coe v1)) (coe d_embed_398 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_146 v1
        -> coe C_Pμ'45'type_278 (coe d_embedFunctor_396 (coe v1))
      C_ν'45'type_148 v1
        -> coe C_Pν'45'type_280 (coe d_embedFunctor_396 (coe v1))
      C_Int_150 -> coe C_PInt_282
      C_Float_152 -> coe C_PFloat_284
      C_Str_154 -> coe C_PStr_286
      C_Buffer_156 -> coe C_PBuffer_288
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGroundF
d_isGroundF_434 ::
  T_PolyFunctor_254 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_434 v0
  = case coe v0 of
      C_PK_258 v1
        -> let v2 = d_isGround_438 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_260
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__262 v1 v2
        -> let v3 = d_isGroundF_434 (coe v1) in
           coe
             (let v4 = d_isGroundF_434 (coe v2) in
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
      C__P'8855'__264 v1 v2
        -> let v3 = d_isGroundF_434 (coe v1) in
           coe
             (let v4 = d_isGroundF_434 (coe v2) in
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
d_isGround_438 ::
  T_PolyType_256 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_438 v0
  = case coe v0 of
      C_PUnit_266
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_268
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__270 v1 v2
        -> let v3 = d_isGround_438 (coe v1) in
           coe
             (let v4 = d_isGround_438 (coe v2) in
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
      C__P'43'__272 v1 v2
        -> let v3 = d_isGround_438 (coe v1) in
           coe
             (let v4 = d_isGround_438 (coe v2) in
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
      C__P'8658''91'_'93'__274 v1 v2 v3
        -> let v4 = d_isGround_438 (coe v1) in
           coe
             (let v5 = d_isGround_438 (coe v3) in
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
      C_PEff_276 v1 v2
        -> let v3 = d_isGround_438 (coe v1) in
           coe
             (let v4 = d_isGround_438 (coe v2) in
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
      C_Pμ'45'type_278 v1
        -> let v2 = d_isGroundF_434 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_280 v1
        -> let v2 = d_isGroundF_434 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_282
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_284
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PStr_286
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PBuffer_288
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_290 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_596 ::
  T_PolyType_256 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_596 v0
  = case coe v0 of
      C_PUnit_266 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_268 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__270 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_596 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_596 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__272 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_596 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_596 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__274 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_596 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showQuantity_34 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\8594 " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showPolyType_596 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_276 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_596 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_596 (coe v2))))
      C_Pμ'45'type_278 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_598 (coe v1))
      C_Pν'45'type_280 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_598 (coe v1))
      C_PInt_282 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_284 -> coe ("Float" :: Data.Text.Text)
      C_PStr_286 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_288 -> coe ("Buffer" :: Data.Text.Text)
      C_PTVar_290 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_598 ::
  T_PolyFunctor_254 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_598 v0
  = case coe v0 of
      C_PK_258 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_596 (coe v1)) (")" :: Data.Text.Text))
      C_PId_260 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__262 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_598 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_598 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__264 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_598 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_598 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_634 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_634 v0 v1
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
d_purityEqBool_636 :: T_Purity_36 -> T_Purity_36 -> Bool
d_purityEqBool_636 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_pure_38
           -> case coe v1 of
                C_pure_38 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_eff_40
           -> case coe v1 of
                C_eff_40 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.typeEqBool
d_typeEqBool_638 :: T_Type_126 -> T_Type_126 -> Bool
d_typeEqBool_638 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_Unit_136
           -> case coe v1 of
                C_Unit_136 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Void_138
           -> case coe v1 of
                C_Void_138 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'42'__140 v3 v4
           -> case coe v1 of
                C__'42'__140 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_638 (coe v3) (coe v5))
                       (coe d_typeEqBool_638 (coe v4) (coe v6))
                _ -> coe v2
         C__'43'__142 v3 v4
           -> case coe v1 of
                C__'43'__142 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_638 (coe v3) (coe v5))
                       (coe d_typeEqBool_638 (coe v4) (coe v6))
                _ -> coe v2
         C__'8658''91'_'93'__144 v3 v4 v5
           -> case coe v4 of
                C_mk'45'kind_54 v6 v7
                  -> case coe v1 of
                       C__'8658''91'_'93'__144 v8 v9 v10
                         -> case coe v9 of
                              C_mk'45'kind_54 v11 v12
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_quantityEqBool_634 (coe v6) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_purityEqBool_636 (coe v7) (coe v12))
                                        (coe
                                           MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                           (coe d_typeEqBool_638 (coe v3) (coe v8))
                                           (coe d_typeEqBool_638 (coe v5) (coe v10))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         C_μ'45'type_146 v3
           -> case coe v1 of
                C_μ'45'type_146 v4 -> coe d_functorEqBool_640 (coe v3) (coe v4)
                _ -> coe v2
         C_ν'45'type_148 v3
           -> case coe v1 of
                C_ν'45'type_148 v4 -> coe d_functorEqBool_640 (coe v3) (coe v4)
                _ -> coe v2
         C_Int_150
           -> case coe v1 of
                C_Int_150 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Float_152
           -> case coe v1 of
                C_Float_152 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Str_154
           -> case coe v1 of
                C_Str_154 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Buffer_156
           -> case coe v1 of
                C_Buffer_156 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.functorEqBool
d_functorEqBool_640 :: T_Functor_124 -> T_Functor_124 -> Bool
d_functorEqBool_640 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_K_128 v3
           -> case coe v1 of
                C_K_128 v4 -> coe d_typeEqBool_638 (coe v3) (coe v4)
                _ -> coe v2
         C_Id_130
           -> case coe v1 of
                C_Id_130 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8853'__132 v3 v4
           -> case coe v1 of
                C__'8853'__132 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_640 (coe v3) (coe v5))
                       (coe d_functorEqBool_640 (coe v4) (coe v6))
                _ -> coe v2
         C__'8855'__134 v3 v4
           -> case coe v1 of
                C__'8855'__134 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_640 (coe v3) (coe v5))
                       (coe d_functorEqBool_640 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Subst
d_Subst_702 :: ()
d_Subst_702 = erased
-- Once.Type._._×'_
d__'215'''__708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'''__708 = erased
-- Once.Type.lookupSubst
d_lookupSubst_710 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_Type_126
d_lookupSubst_710 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_710 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extendSubst
d_extendSubst_744 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Type_126 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_744 v0 v1 v2
  = let v3 = d_lookupSubst_710 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_typeEqBool_638 (coe v1) (coe v4))
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
d_instantiate_774 ::
  T_PolyType_256 ->
  T_Type_126 -> Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_774 v0 v1
  = coe
      d_instantiateAcc_776 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.instantiateAcc
d_instantiateAcc_776 ::
  T_PolyType_256 ->
  T_Type_126 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_776 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PUnit_266
           -> case coe v1 of
                C_Unit_136
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PVoid_268
           -> case coe v1 of
                C_Void_138
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'42'__270 v4 v5
           -> case coe v1 of
                C__'42'__140 v6 v7
                  -> let v8 = d_instantiateAcc_776 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_776 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'43'__272 v4 v5
           -> case coe v1 of
                C__'43'__142 v6 v7
                  -> let v8 = d_instantiateAcc_776 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_776 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8658''91'_'93'__274 v4 v5 v6
           -> case coe v1 of
                C__'8658''91'_'93'__144 v7 v8 v9
                  -> case coe v8 of
                       C_mk'45'kind_54 v10 v11
                         -> case coe v11 of
                              C_pure_38
                                -> let v12 = d_quantityEqBool_634 (coe v5) (coe v10) in
                                   coe
                                     (if coe v12
                                        then let v13
                                                   = d_instantiateAcc_776
                                                       (coe v4) (coe v7) (coe v2) in
                                             coe
                                               (case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                    -> coe
                                                         d_instantiateAcc_776 (coe v6) (coe v9)
                                                         (coe v14)
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v13
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         C_PEff_276 v4 v5
           -> case coe v1 of
                C__'8658''91'_'93'__144 v6 v7 v8
                  -> case coe v7 of
                       C_mk'45'kind_54 v9 v10
                         -> case coe v10 of
                              C_eff_40
                                -> let v11 = d_instantiateAcc_776 (coe v4) (coe v6) (coe v2) in
                                   coe
                                     (case coe v11 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                          -> coe d_instantiateAcc_776 (coe v5) (coe v8) (coe v12)
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         C_Pμ'45'type_278 v4
           -> case coe v1 of
                C_μ'45'type_146 v5
                  -> coe d_instantiateFunctor_778 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_Pν'45'type_280 v4
           -> case coe v1 of
                C_ν'45'type_148 v5
                  -> coe d_instantiateFunctor_778 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PInt_282
           -> case coe v1 of
                C_Int_150 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PFloat_284
           -> case coe v1 of
                C_Float_152
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PStr_286
           -> case coe v1 of
                C_Str_154 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PBuffer_288
           -> case coe v1 of
                C_Buffer_156
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PTVar_290 v4 -> coe d_extendSubst_744 (coe v4) (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.instantiateFunctor
d_instantiateFunctor_778 ::
  T_PolyFunctor_254 ->
  T_Functor_124 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_778 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PK_258 v4
           -> case coe v1 of
                C_K_128 v5 -> coe d_instantiateAcc_776 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PId_260
           -> case coe v1 of
                C_Id_130 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'8853'__262 v4 v5
           -> case coe v1 of
                C__'8853'__132 v6 v7
                  -> let v8 = d_instantiateFunctor_778 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_778 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8855'__264 v4 v5
           -> case coe v1 of
                C__'8855'__134 v6 v7
                  -> let v8 = d_instantiateFunctor_778 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_778 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.applySubst
d_applySubst_1082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyType_256 -> Maybe T_Type_126
d_applySubst_1082 v0 v1
  = case coe v1 of
      C_PUnit_266
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_136)
      C_PVoid_268
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_138)
      C__P'42'__270 v2 v3
        -> let v4 = d_applySubst_1082 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1082 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'42'__140 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'43'__272 v2 v3
        -> let v4 = d_applySubst_1082 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1082 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'43'__142 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8658''91'_'93'__274 v2 v3 v4
        -> let v5 = d_applySubst_1082 (coe v0) (coe v2) in
           coe
             (let v6 = d_applySubst_1082 (coe v0) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C__'8658''91'_'93'__144 (coe v7)
                                    (coe C_mk'45'kind_54 (coe v3) (coe C_pure_38)) (coe v8))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_PEff_276 v2 v3
        -> let v4 = d_applySubst_1082 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_1082 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    C__'8658''91'_'93'__144 (coe v6)
                                    (coe C_mk'45'kind_54 (coe C_Many_10) (coe C_eff_40)) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_Pμ'45'type_278 v2
        -> let v3 = d_applySubstFunctor_1084 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_μ'45'type_146 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_280 v2
        -> let v3 = d_applySubstFunctor_1084 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_ν'45'type_148 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_282
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_150)
      C_PFloat_284
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_152)
      C_PStr_286
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_154)
      C_PBuffer_288
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_156)
      C_PTVar_290 v2 -> coe d_lookupSubst_710 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubstFunctor
d_applySubstFunctor_1084 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyFunctor_254 -> Maybe T_Functor_124
d_applySubstFunctor_1084 v0 v1
  = case coe v1 of
      C_PK_258 v2
        -> let v3 = d_applySubst_1082 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_128 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_260
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_130)
      C__P'8853'__262 v2 v3
        -> let v4 = d_applySubstFunctor_1084 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1084 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8853'__132 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8855'__264 v2 v3
        -> let v4 = d_applySubstFunctor_1084 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1084 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8855'__134 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.schemaArrowCodomain
d_schemaArrowCodomain_1306 ::
  T_PolyType_256 -> T_Type_126 -> Maybe T_Type_126
d_schemaArrowCodomain_1306 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C__P'8658''91'_'93'__274 v3 v4 v5
           -> let v6
                    = d_instantiateAcc_776
                        (coe v3) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> coe d_applySubst_1082 (coe v7) (coe v5)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
