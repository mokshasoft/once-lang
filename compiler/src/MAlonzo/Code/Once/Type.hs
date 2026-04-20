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
import qualified MAlonzo.Code.Data.String.Base
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
-- Once.Type.Functor
d_Functor_36 = ()
data T_Functor_36
  = C_K_40 T_Type_38 | C_Id_42 |
    C__'8853'__44 T_Functor_36 T_Functor_36 |
    C__'8855'__46 T_Functor_36 T_Functor_36
-- Once.Type.Type
d_Type_38 = ()
data T_Type_38
  = C_Unit_48 | C_Void_50 | C__'42'__52 T_Type_38 T_Type_38 |
    C__'43'__54 T_Type_38 T_Type_38 |
    C__'8658''91'_'93'__56 T_Type_38 T_Quantity_4 T_Type_38 |
    C_Eff_58 T_Type_38 T_Type_38 | C_μ'45'type_60 T_Functor_36 |
    C_ν'45'type_62 T_Functor_36 | C_Int_64 | C_Float_66 | C_Str_68 |
    C_Buffer_70
-- Once.Type._⊸_
d__'8888'__72 :: T_Type_38 -> T_Type_38 -> T_Type_38
d__'8888'__72 v0 v1
  = coe C__'8658''91'_'93'__56 (coe v0) (coe C_One_8) (coe v1)
-- Once.Type._⇒_
d__'8658'__78 :: T_Type_38 -> T_Type_38 -> T_Type_38
d__'8658'__78 v0 v1
  = coe C__'8658''91'_'93'__56 (coe v0) (coe C_Many_10) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__84 :: T_Type_38 -> T_Type_38 -> T_Type_38
d__'8658''8320'__84 v0 v1
  = coe C__'8658''91'_'93'__56 (coe v0) (coe C_Zero_6) (coe v1)
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_90 :: T_Functor_36 -> T_Type_38 -> T_Type_38
d_'10214'_'10215'T_90 v0 v1
  = case coe v0 of
      C_K_40 v2 -> coe v2
      C_Id_42 -> coe v1
      C__'8853'__44 v2 v3
        -> coe
             C__'43'__54 (coe d_'10214'_'10215'T_90 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_90 (coe v3) (coe v1))
      C__'8855'__46 v2 v3
        -> coe
             C__'42'__52 (coe d_'10214'_'10215'T_90 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_90 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_110 :: T_Functor_36
d_NatF_110
  = coe C__'8853'__44 (coe C_K_40 (coe C_Unit_48)) (coe C_Id_42)
-- Once.Type.ListF
d_ListF_112 :: T_Type_38 -> T_Functor_36
d_ListF_112 v0
  = coe
      C__'8853'__44 (coe C_K_40 (coe C_Unit_48))
      (coe C__'8855'__46 (coe C_K_40 (coe v0)) (coe C_Id_42))
-- Once.Type.TreeF
d_TreeF_116 :: T_Type_38 -> T_Functor_36
d_TreeF_116 v0
  = coe
      C__'8853'__44 (coe C_K_40 (coe v0))
      (coe C__'8855'__46 (coe C_Id_42) (coe C_Id_42))
-- Once.Type.IsPrimitive
d_IsPrimitive_120 a0 = ()
data T_IsPrimitive_120
  = C_is'45'unit_122 | C_is'45'int_124 | C_is'45'float_126 |
    C_is'45'str_128 | C_is'45'buffer_130
-- Once.Type.showType
d_showType_132 ::
  T_Type_38 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_132 v0
  = case coe v0 of
      C_Unit_48 -> coe ("Unit" :: Data.Text.Text)
      C_Void_50 -> coe ("Void" :: Data.Text.Text)
      C__'42'__52 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_132 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__54 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_132 (coe v2)) (")" :: Data.Text.Text))))
      C__'8658''91'_'93'__56 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_132 (coe v1))
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
                            (d_showType_132 (coe v3)) (")" :: Data.Text.Text))))))
      C_Eff_58 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_132 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showType_132 (coe v2))))
      C_μ'45'type_60 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_134 (coe v1))
      C_ν'45'type_62 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_134 (coe v1))
      C_Int_64 -> coe ("Int" :: Data.Text.Text)
      C_Float_66 -> coe ("Float" :: Data.Text.Text)
      C_Str_68 -> coe ("String" :: Data.Text.Text)
      C_Buffer_70 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_134 ::
  T_Functor_36 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_134 v0
  = case coe v0 of
      C_K_40 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_132 (coe v1)) (")" :: Data.Text.Text))
      C_Id_42 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__44 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_134 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__46 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_134 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_134 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
