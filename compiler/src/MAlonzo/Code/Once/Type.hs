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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Type._≟q_
d__'8799'q__8 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'q__8 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showQuantity
d_showQuantity_10 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
        -> coe ("\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPurity
d_showPurity_12 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPurity_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> coe ("pure" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe ("eff" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showArrowKind
d_showArrowKind_14 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArrowKind_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showQuantity_10 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("," :: Data.Text.Text) (d_showPurity_12 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._≟p_
d__'8799'p__24 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'p__24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.≟k-aux
d_'8799'k'45'aux_34 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'k'45'aux_34 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'k'45'aux_34 v4 v5
du_'8799'k'45'aux_34 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'k'45'aux_34 v0 v1
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
d__'8799'k__48 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'k__48 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v4 v5
               -> coe
                    du_'8799'k'45'aux_34 (coe d__'8799'q__8 (coe v2) (coe v4))
                    (coe d__'8799'p__24 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_58 :: MAlonzo.Code.Once.Spec.Type.T_Functor_6
d_NatF_58
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16
      (coe
         MAlonzo.Code.Once.Spec.Type.C_K_12
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Spec.Type.C_Id_14)
-- Once.Type.ListF
d_ListF_60 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6
d_ListF_60 v0
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16
      (coe
         MAlonzo.Code.Once.Spec.Type.C_K_12
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8855'__18
         (coe MAlonzo.Code.Once.Spec.Type.C_K_12 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_14))
-- Once.Type.TreeF
d_TreeF_64 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6
d_TreeF_64 v0
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16
      (coe MAlonzo.Code.Once.Spec.Type.C_K_12 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8855'__18
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_14)
         (coe MAlonzo.Code.Once.Spec.Type.C_Id_14))
-- Once.Type.FitsInReg
d_FitsInReg_68 a0 = ()
data T_FitsInReg_68 = C_fits'45'int_70 | C_fits'45'float_72
-- Once.Type.fits-in-reg?
d_fits'45'in'45'reg'63'_76 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> Maybe T_FitsInReg_68
d_fits'45'in'45'reg'63'_76 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Int_34
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'int_70)
         MAlonzo.Code.Once.Spec.Type.C_Float_36
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_fits'45'float_72)
         _ -> coe v1)
-- Once.Type.showType
d_showType_78 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_78 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_20
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C_Void_22
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_78 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_78 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_78 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_78 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_78 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_showQuantity_10 (coe v4))
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("\8594 " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          (d_showType_78 (coe v3)) (")" :: Data.Text.Text))))))
                    MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("Eff " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showType_78 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text) (d_showType_78 (coe v3))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_80 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showFunctor_80 (coe v1))
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Eff " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showFunctor_80 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_34
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C_Float_36
        -> coe ("Float" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C_rigid_38 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_k'45'base_40
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'b" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             MAlonzo.Code.Once.Spec.Type.C_k'45'any_42
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("'a" :: Data.Text.Text)
                    (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_80 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_80 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_78 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.C_Id_14 -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_80 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_80 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_80 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_80 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.both-ground
d_both'45'ground_124 ::
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_both'45'ground_124 ~v0 ~v1 v2 v3 = du_both'45'ground_124 v2 v3
du_both'45'ground_124 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_both'45'ground_124 v0 v1
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
d_isGroundF_132 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_132 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PK_12 v1
        -> coe d_isGround_136 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8853'__16 v1 v2
        -> coe
             du_both'45'ground_124 (coe d_isGroundF_132 (coe v1))
             (coe d_isGroundF_132 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8855'__18 v1 v2
        -> coe
             du_both'45'ground_124 (coe d_isGroundF_132 (coe v1))
             (coe d_isGroundF_132 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGround
d_isGround_136 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_136 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PUnit_20
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PVoid_22
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'42'__24 v1 v2
        -> coe
             du_both'45'ground_124 (coe d_isGround_136 (coe v1))
             (coe d_isGround_136 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'43'__26 v1 v2
        -> coe
             du_both'45'ground_124 (coe d_isGround_136 (coe v1))
             (coe d_isGround_136 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             du_both'45'ground_124 (coe d_isGround_136 (coe v1))
             (coe d_isGround_136 (coe v3))
      MAlonzo.Code.Once.Spec.Type.Poly.C_PEff_30 v1 v2
        -> coe
             du_both'45'ground_124 (coe d_isGround_136 (coe v1))
             (coe d_isGround_136 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pμ'45'type_32 v1
        -> coe d_isGroundF_132 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pν'45'type_34 v1 v2
        -> coe d_isGroundF_132 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PInt_36
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PFloat_38
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PTVar_40 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_168 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_168 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PUnit_20
        -> coe ("Unit" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PVoid_22
        -> coe ("Void" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_168 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_168 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_168 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_168 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_168 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showQuantity_10 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("\8594 " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_showPolyType_168 (coe v3)) (")" :: Data.Text.Text))))))
      MAlonzo.Code.Once.Spec.Type.Poly.C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_168 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_168 (coe v2))))
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pμ'45'type_32 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_170 (coe v1))
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pν'45'type_34 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 " :: Data.Text.Text) (d_showPolyFunctor_170 (coe v1))
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("\957 (Eff " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showPolyFunctor_170 (coe v1)) (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Poly.C_PInt_36
        -> coe ("Int" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PFloat_38
        -> coe ("Float" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PTVar_40 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_170 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_170 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PK_12 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_168 (coe v1)) (")" :: Data.Text.Text))
      MAlonzo.Code.Once.Spec.Type.Poly.C_PId_14
        -> coe ("Id" :: Data.Text.Text)
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_170 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_170 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_170 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_170 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_208 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 -> Bool
d_quantityEqBool_208 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.purityEqBool
d_purityEqBool_210 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 -> Bool
d_purityEqBool_210 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.tkindEqBool
d_tkindEqBool_212 ::
  MAlonzo.Code.Once.Spec.Type.T_TKind_10 ->
  MAlonzo.Code.Once.Spec.Type.T_TKind_10 -> Bool
d_tkindEqBool_212 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_k'45'base_40
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_k'45'base_40
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C_k'45'any_42
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_k'45'any_42
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_k'45'base_40
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_k'45'any_42
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.typeEqBool
d_typeEqBool_214 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> Bool
d_typeEqBool_214 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_20
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Void_22
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_214 (coe v2) (coe v4))
                    (coe d_typeEqBool_214 (coe v3) (coe v5))
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_typeEqBool_214 (coe v2) (coe v4))
                    (coe d_typeEqBool_214 (coe v3) (coe v5))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v8 v9
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v10 v11
                             -> coe
                                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                  (coe d_quantityEqBool_208 (coe v8) (coe v10))
                                  (coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe d_purityEqBool_210 (coe v9) (coe v11))
                                     (coe
                                        MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                        (coe d_typeEqBool_214 (coe v2) (coe v5))
                                        (coe d_typeEqBool_214 (coe v4) (coe v7))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v3
               -> coe d_functorEqBool_216 (coe v2) (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_purityEqBool_210 (coe v3) (coe v5))
                    (coe d_functorEqBool_216 (coe v2) (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Int_34
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Float_36
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C_rigid_38 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_rigid_38 v2 v3
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Spec.Type.C_rigid_38 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_tkindEqBool_212 (coe v2) (coe v5))
                       (coe eqInt (coe v3) (coe v6))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.functorEqBool
d_functorEqBool_216 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> Bool
d_functorEqBool_216 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_12 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v3
               -> coe d_typeEqBool_214 (coe v2) (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_Id_14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v2
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_216 (coe v2) (coe v4))
                    (coe d_functorEqBool_216 (coe v3) (coe v5))
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe d_functorEqBool_216 (coe v2) (coe v4))
                    (coe d_functorEqBool_216 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
