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

module MAlonzo.Code.Once.Spec.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Spec.Type.Functor
d_Functor_6 = ()
data T_Functor_6
  = C_K_12 T_Type_8 | C_Id_14 |
    C__'8853'__16 T_Functor_6 T_Functor_6 |
    C__'8855'__18 T_Functor_6 T_Functor_6
-- Once.Spec.Type.Type
d_Type_8 = ()
data T_Type_8
  = C_Unit_20 | C_Void_22 | C__'42'__24 T_Type_8 T_Type_8 |
    C__'43'__26 T_Type_8 T_Type_8 |
    C__'8658''91'_'93'__28 T_Type_8
                           MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 T_Type_8 |
    C_μ'45'type_30 T_Functor_6 |
    C_ν'45'type_32 T_Functor_6
                   MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 |
    C_Int_34 | C_Float_36 | C_rigid_38 T_TKind_10 Integer
-- Once.Spec.Type.TKind
d_TKind_10 = ()
data T_TKind_10 = C_k'45'base_40 | C_k'45'any_42
-- Once.Spec.Type._⊸_
d__'8888'__44 :: T_Type_8 -> T_Type_8 -> T_Type_8
d__'8888'__44 v0 v1
  = coe
      C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
      (coe v1)
-- Once.Spec.Type._⇒_
d__'8658'__50 :: T_Type_8 -> T_Type_8 -> T_Type_8
d__'8658'__50 v0 v1
  = coe
      C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
      (coe v1)
-- Once.Spec.Type._⇒₀_
d__'8658''8320'__56 :: T_Type_8 -> T_Type_8 -> T_Type_8
d__'8658''8320'__56 v0 v1
  = coe
      C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
      (coe v1)
-- Once.Spec.Type.⟦_⟧T
d_'10214'_'10215'T_62 :: T_Functor_6 -> T_Type_8 -> T_Type_8
d_'10214'_'10215'T_62 v0 v1
  = case coe v0 of
      C_K_12 v2 -> coe v2
      C_Id_14 -> coe v1
      C__'8853'__16 v2 v3
        -> coe
             C__'43'__26 (coe d_'10214'_'10215'T_62 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_62 (coe v3) (coe v1))
      C__'8855'__18 v2 v3
        -> coe
             C__'42'__24 (coe d_'10214'_'10215'T_62 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_62 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.isVoid?
d_isVoid'63'_84 ::
  T_Type_8 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isVoid'63'_84 v0
  = case coe v0 of
      C_Unit_20
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Void_22
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_ν'45'type_32 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Int_34
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Float_36
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_rigid_38 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.isUnit?
d_isUnit'63'_88 ::
  T_Type_8 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isUnit'63'_88 v0
  = case coe v0 of
      C_Unit_20
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      C_Void_22
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C__'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_ν'45'type_32 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Int_34
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_Float_36
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_rigid_38 v1 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
