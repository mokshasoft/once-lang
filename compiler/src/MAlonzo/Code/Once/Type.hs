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
-- Once.Type.Functor
d_Functor_32 = ()
data T_Functor_32
  = C_K_36 T_Type_34 | C_Id_38 |
    C__'8853'__40 T_Functor_32 T_Functor_32 |
    C__'8855'__42 T_Functor_32 T_Functor_32
-- Once.Type.Type
d_Type_34 = ()
data T_Type_34
  = C_Unit_44 | C_Void_46 | C__'42'__48 T_Type_34 T_Type_34 |
    C__'43'__50 T_Type_34 T_Type_34 |
    C__'8658''91'_'93'__52 T_Type_34 T_Quantity_4 T_Type_34 |
    C_Eff_54 T_Type_34 T_Type_34 | C_μ'45'type_56 T_Functor_32 |
    C_ν'45'type_58 T_Functor_32 | C_Int_60 | C_Float_62 | C_Str_64 |
    C_Buffer_66
-- Once.Type.PolyFunctor
d_PolyFunctor_68 = ()
data T_PolyFunctor_68
  = C_PK_72 T_PolyType_70 | C_PId_74 |
    C__P'8853'__76 T_PolyFunctor_68 T_PolyFunctor_68 |
    C__P'8855'__78 T_PolyFunctor_68 T_PolyFunctor_68
-- Once.Type.PolyType
d_PolyType_70 = ()
data T_PolyType_70
  = C_PUnit_80 | C_PVoid_82 |
    C__P'42'__84 T_PolyType_70 T_PolyType_70 |
    C__P'43'__86 T_PolyType_70 T_PolyType_70 |
    C__P'8658''91'_'93'__88 T_PolyType_70 T_Quantity_4 T_PolyType_70 |
    C_PEff_90 T_PolyType_70 T_PolyType_70 |
    C_Pμ'45'type_92 T_PolyFunctor_68 |
    C_Pν'45'type_94 T_PolyFunctor_68 | C_PInt_96 | C_PFloat_98 |
    C_PStr_100 | C_PBuffer_102 |
    C_TVar_104 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.embedFunctor
d_embedFunctor_106 :: T_Functor_32 -> T_PolyFunctor_68
d_embedFunctor_106 v0
  = case coe v0 of
      C_K_36 v1 -> coe C_PK_72 (coe d_embed_108 (coe v1))
      C_Id_38 -> coe C_PId_74
      C__'8853'__40 v1 v2
        -> coe
             C__P'8853'__76 (coe d_embedFunctor_106 (coe v1))
             (coe d_embedFunctor_106 (coe v2))
      C__'8855'__42 v1 v2
        -> coe
             C__P'8855'__78 (coe d_embedFunctor_106 (coe v1))
             (coe d_embedFunctor_106 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_108 :: T_Type_34 -> T_PolyType_70
d_embed_108 v0
  = case coe v0 of
      C_Unit_44 -> coe C_PUnit_80
      C_Void_46 -> coe C_PVoid_82
      C__'42'__48 v1 v2
        -> coe
             C__P'42'__84 (coe d_embed_108 (coe v1)) (coe d_embed_108 (coe v2))
      C__'43'__50 v1 v2
        -> coe
             C__P'43'__86 (coe d_embed_108 (coe v1)) (coe d_embed_108 (coe v2))
      C__'8658''91'_'93'__52 v1 v2 v3
        -> coe
             C__P'8658''91'_'93'__88 (coe d_embed_108 (coe v1)) (coe v2)
             (coe d_embed_108 (coe v3))
      C_Eff_54 v1 v2
        -> coe
             C_PEff_90 (coe d_embed_108 (coe v1)) (coe d_embed_108 (coe v2))
      C_μ'45'type_56 v1
        -> coe C_Pμ'45'type_92 (coe d_embedFunctor_106 (coe v1))
      C_ν'45'type_58 v1
        -> coe C_Pν'45'type_94 (coe d_embedFunctor_106 (coe v1))
      C_Int_60 -> coe C_PInt_96
      C_Float_62 -> coe C_PFloat_98
      C_Str_64 -> coe C_PStr_100
      C_Buffer_66 -> coe C_PBuffer_102
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractFunctor
d_extractFunctor_142 :: T_PolyFunctor_68 -> Maybe T_Functor_32
d_extractFunctor_142 v0
  = case coe v0 of
      C_PK_72 v1
        -> let v2 = d_extract_144 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_36 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_74
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_38)
      C__P'8853'__76 v1 v2
        -> let v3 = d_extractFunctor_142 (coe v1) in
           coe
             (let v4 = d_extractFunctor_142 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8853'__40 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8855'__78 v1 v2
        -> let v3 = d_extractFunctor_142 (coe v1) in
           coe
             (let v4 = d_extractFunctor_142 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8855'__42 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extract
d_extract_144 :: T_PolyType_70 -> Maybe T_Type_34
d_extract_144 v0
  = case coe v0 of
      C_PUnit_80
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_44)
      C_PVoid_82
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_46)
      C__P'42'__84 v1 v2
        -> let v3 = d_extract_144 (coe v1) in
           coe
             (let v4 = d_extract_144 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'42'__48 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'43'__86 v1 v2
        -> let v3 = d_extract_144 (coe v1) in
           coe
             (let v4 = d_extract_144 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'43'__50 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8658''91'_'93'__88 v1 v2 v3
        -> let v4 = d_extract_144 (coe v1) in
           coe
             (let v5 = d_extract_144 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8658''91'_'93'__52 (coe v6) (coe v2) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_PEff_90 v1 v2
        -> let v3 = d_extract_144 (coe v1) in
           coe
             (let v4 = d_extract_144 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C_Eff_54 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_Pμ'45'type_92 v1
        -> let v2 = d_extractFunctor_142 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_μ'45'type_56 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_94 v1
        -> let v2 = d_extractFunctor_142 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_ν'45'type_58 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_96
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_60)
      C_PFloat_98
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_62)
      C_PStr_100
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_64)
      C_PBuffer_102
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_66)
      C_TVar_104 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type._⊸_
d__'8888'__308 :: T_Type_34 -> T_Type_34 -> T_Type_34
d__'8888'__308 v0 v1
  = coe C__'8658''91'_'93'__52 (coe v0) (coe C_One_8) (coe v1)
-- Once.Type._⇒_
d__'8658'__314 :: T_Type_34 -> T_Type_34 -> T_Type_34
d__'8658'__314 v0 v1
  = coe C__'8658''91'_'93'__52 (coe v0) (coe C_Many_10) (coe v1)
-- Once.Type._⇒₀_
d__'8658''8320'__320 :: T_Type_34 -> T_Type_34 -> T_Type_34
d__'8658''8320'__320 v0 v1
  = coe C__'8658''91'_'93'__52 (coe v0) (coe C_Zero_6) (coe v1)
-- Once.Type.⟦_⟧T
d_'10214'_'10215'T_326 :: T_Functor_32 -> T_Type_34 -> T_Type_34
d_'10214'_'10215'T_326 v0 v1
  = case coe v0 of
      C_K_36 v2 -> coe v2
      C_Id_38 -> coe v1
      C__'8853'__40 v2 v3
        -> coe
             C__'43'__50 (coe d_'10214'_'10215'T_326 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_326 (coe v3) (coe v1))
      C__'8855'__42 v2 v3
        -> coe
             C__'42'__48 (coe d_'10214'_'10215'T_326 (coe v2) (coe v1))
             (coe d_'10214'_'10215'T_326 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.NatF
d_NatF_346 :: T_Functor_32
d_NatF_346
  = coe C__'8853'__40 (coe C_K_36 (coe C_Unit_44)) (coe C_Id_38)
-- Once.Type.ListF
d_ListF_348 :: T_Type_34 -> T_Functor_32
d_ListF_348 v0
  = coe
      C__'8853'__40 (coe C_K_36 (coe C_Unit_44))
      (coe C__'8855'__42 (coe C_K_36 (coe v0)) (coe C_Id_38))
-- Once.Type.TreeF
d_TreeF_352 :: T_Type_34 -> T_Functor_32
d_TreeF_352 v0
  = coe
      C__'8853'__40 (coe C_K_36 (coe v0))
      (coe C__'8855'__42 (coe C_Id_38) (coe C_Id_38))
-- Once.Type.IsPrimitive
d_IsPrimitive_356 a0 = ()
data T_IsPrimitive_356
  = C_is'45'unit_358 | C_is'45'int_360 | C_is'45'float_362 |
    C_is'45'str_364 | C_is'45'buffer_366
-- Once.Type.showType
d_showType_368 ::
  T_Type_34 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showType_368 v0
  = case coe v0 of
      C_Unit_44 -> coe ("Unit" :: Data.Text.Text)
      C_Void_46 -> coe ("Void" :: Data.Text.Text)
      C__'42'__48 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_368 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_368 (coe v2)) (")" :: Data.Text.Text))))
      C__'43'__50 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_368 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showType_368 (coe v2)) (")" :: Data.Text.Text))))
      C__'8658''91'_'93'__52 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_368 (coe v1))
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
                            (d_showType_368 (coe v3)) (")" :: Data.Text.Text))))))
      C_Eff_54 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_368 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showType_368 (coe v2))))
      C_μ'45'type_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showFunctor_370 (coe v1))
      C_ν'45'type_58 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showFunctor_370 (coe v1))
      C_Int_60 -> coe ("Int" :: Data.Text.Text)
      C_Float_62 -> coe ("Float" :: Data.Text.Text)
      C_Str_64 -> coe ("String" :: Data.Text.Text)
      C_Buffer_66 -> coe ("Buffer" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showFunctor
d_showFunctor_370 ::
  T_Functor_32 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunctor_370 v0
  = case coe v0 of
      C_K_36 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showType_368 (coe v1)) (")" :: Data.Text.Text))
      C_Id_38 -> coe ("Id" :: Data.Text.Text)
      C__'8853'__40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_370 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_370 (coe v2)) (")" :: Data.Text.Text))))
      C__'8855'__42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showFunctor_370 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showFunctor_370 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_404 ::
  T_PolyType_70 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_404 v0
  = case coe v0 of
      C_PUnit_80 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_82 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__84 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_404 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_404 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__86 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_404 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_404 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__88 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_404 (coe v1))
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
                            (d_showPolyType_404 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_90 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_404 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_404 (coe v2))))
      C_Pμ'45'type_92 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_406 (coe v1))
      C_Pν'45'type_94 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_406 (coe v1))
      C_PInt_96 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_98 -> coe ("Float" :: Data.Text.Text)
      C_PStr_100 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_102 -> coe ("Buffer" :: Data.Text.Text)
      C_TVar_104 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_406 ::
  T_PolyFunctor_68 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_406 v0
  = case coe v0 of
      C_PK_72 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_404 (coe v1)) (")" :: Data.Text.Text))
      C_PId_74 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__76 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_406 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_406 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__78 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_406 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_406 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
