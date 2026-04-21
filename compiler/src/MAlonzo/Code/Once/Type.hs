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
-- Once.Type.PolyFunctor
d_PolyFunctor_168 = ()
data T_PolyFunctor_168
  = C_PK_172 T_PolyType_170 | C_PId_174 |
    C__P'8853'__176 T_PolyFunctor_168 T_PolyFunctor_168 |
    C__P'8855'__178 T_PolyFunctor_168 T_PolyFunctor_168
-- Once.Type.PolyType
d_PolyType_170 = ()
data T_PolyType_170
  = C_PUnit_180 | C_PVoid_182 |
    C__P'42'__184 T_PolyType_170 T_PolyType_170 |
    C__P'43'__186 T_PolyType_170 T_PolyType_170 |
    C__P'8658''91'_'93'__188 T_PolyType_170 T_Quantity_4
                             T_PolyType_170 |
    C_PEff_190 T_PolyType_170 T_PolyType_170 |
    C_Pμ'45'type_192 T_PolyFunctor_168 |
    C_Pν'45'type_194 T_PolyFunctor_168 | C_PInt_196 | C_PFloat_198 |
    C_PStr_200 | C_PBuffer_202 |
    C_PTVar_204 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Type.GroundF
d_GroundF_206 :: T_PolyFunctor_168 -> ()
d_GroundF_206 = erased
-- Once.Type.Ground
d_Ground_208 :: T_PolyType_170 -> ()
d_Ground_208 = erased
-- Once.Type.extractGroundF
d_extractGroundF_242 ::
  T_PolyFunctor_168 -> AgdaAny -> T_Functor_36
d_extractGroundF_242 v0 v1
  = case coe v0 of
      C_PK_172 v2
        -> coe C_K_40 (coe d_extractGround_246 (coe v2) (coe v1))
      C_PId_174 -> coe C_Id_42
      C__P'8853'__176 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8853'__44 (coe d_extractGroundF_242 (coe v2) (coe v4))
                    (coe d_extractGroundF_242 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__178 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'8855'__46 (coe d_extractGroundF_242 (coe v2) (coe v4))
                    (coe d_extractGroundF_242 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extractGround
d_extractGround_246 :: T_PolyType_170 -> AgdaAny -> T_Type_38
d_extractGround_246 v0 v1
  = case coe v0 of
      C_PUnit_180 -> coe C_Unit_48
      C_PVoid_182 -> coe C_Void_50
      C__P'42'__184 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'42'__52 (coe d_extractGround_246 (coe v2) (coe v4))
                    (coe d_extractGround_246 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__186 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C__'43'__54 (coe d_extractGround_246 (coe v2) (coe v4))
                    (coe d_extractGround_246 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__188 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C__'8658''91'_'93'__56 (coe d_extractGround_246 (coe v2) (coe v5))
                    (coe v3) (coe d_extractGround_246 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_190 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_Eff_58 (coe d_extractGround_246 (coe v2) (coe v4))
                    (coe d_extractGround_246 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_192 v2
        -> coe C_μ'45'type_60 (coe d_extractGroundF_242 (coe v2) (coe v1))
      C_Pν'45'type_194 v2
        -> coe C_ν'45'type_62 (coe d_extractGroundF_242 (coe v2) (coe v1))
      C_PInt_196 -> coe C_Int_64
      C_PFloat_198 -> coe C_Float_66
      C_PStr_200 -> coe C_Str_68
      C_PBuffer_202 -> coe C_Buffer_70
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embedFunctor
d_embedFunctor_310 :: T_Functor_36 -> T_PolyFunctor_168
d_embedFunctor_310 v0
  = case coe v0 of
      C_K_40 v1 -> coe C_PK_172 (coe d_embed_312 (coe v1))
      C_Id_42 -> coe C_PId_174
      C__'8853'__44 v1 v2
        -> coe
             C__P'8853'__176 (coe d_embedFunctor_310 (coe v1))
             (coe d_embedFunctor_310 (coe v2))
      C__'8855'__46 v1 v2
        -> coe
             C__P'8855'__178 (coe d_embedFunctor_310 (coe v1))
             (coe d_embedFunctor_310 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.embed
d_embed_312 :: T_Type_38 -> T_PolyType_170
d_embed_312 v0
  = case coe v0 of
      C_Unit_48 -> coe C_PUnit_180
      C_Void_50 -> coe C_PVoid_182
      C__'42'__52 v1 v2
        -> coe
             C__P'42'__184 (coe d_embed_312 (coe v1)) (coe d_embed_312 (coe v2))
      C__'43'__54 v1 v2
        -> coe
             C__P'43'__186 (coe d_embed_312 (coe v1)) (coe d_embed_312 (coe v2))
      C__'8658''91'_'93'__56 v1 v2 v3
        -> coe
             C__P'8658''91'_'93'__188 (coe d_embed_312 (coe v1)) (coe v2)
             (coe d_embed_312 (coe v3))
      C_Eff_58 v1 v2
        -> coe
             C_PEff_190 (coe d_embed_312 (coe v1)) (coe d_embed_312 (coe v2))
      C_μ'45'type_60 v1
        -> coe C_Pμ'45'type_192 (coe d_embedFunctor_310 (coe v1))
      C_ν'45'type_62 v1
        -> coe C_Pν'45'type_194 (coe d_embedFunctor_310 (coe v1))
      C_Int_64 -> coe C_PInt_196
      C_Float_66 -> coe C_PFloat_198
      C_Str_68 -> coe C_PStr_200
      C_Buffer_70 -> coe C_PBuffer_202
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.isGroundF
d_isGroundF_348 ::
  T_PolyFunctor_168 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGroundF_348 v0
  = case coe v0 of
      C_PK_172 v1
        -> let v2 = d_isGround_352 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_174
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'8853'__176 v1 v2
        -> let v3 = d_isGroundF_348 (coe v1) in
           coe
             (let v4 = d_isGroundF_348 (coe v2) in
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
      C__P'8855'__178 v1 v2
        -> let v3 = d_isGroundF_348 (coe v1) in
           coe
             (let v4 = d_isGroundF_348 (coe v2) in
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
d_isGround_352 ::
  T_PolyType_170 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_isGround_352 v0
  = case coe v0 of
      C_PUnit_180
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PVoid_182
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C__P'42'__184 v1 v2
        -> let v3 = d_isGround_352 (coe v1) in
           coe
             (let v4 = d_isGround_352 (coe v2) in
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
      C__P'43'__186 v1 v2
        -> let v3 = d_isGround_352 (coe v1) in
           coe
             (let v4 = d_isGround_352 (coe v2) in
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
      C__P'8658''91'_'93'__188 v1 v2 v3
        -> let v4 = d_isGround_352 (coe v1) in
           coe
             (let v5 = d_isGround_352 (coe v3) in
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
      C_PEff_190 v1 v2
        -> let v3 = d_isGround_352 (coe v1) in
           coe
             (let v4 = d_isGround_352 (coe v2) in
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
      C_Pμ'45'type_192 v1
        -> let v2 = d_isGroundF_348 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_194 v1
        -> let v2 = d_isGroundF_348 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_196
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PFloat_198
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PStr_200
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PBuffer_202
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_PTVar_204 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyType
d_showPolyType_510 ::
  T_PolyType_170 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyType_510 v0
  = case coe v0 of
      C_PUnit_180 -> coe ("Unit" :: Data.Text.Text)
      C_PVoid_182 -> coe ("Void" :: Data.Text.Text)
      C__P'42'__184 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_510 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" * " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_510 (coe v2)) (")" :: Data.Text.Text))))
      C__P'43'__186 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_510 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" + " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyType_510 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8658''91'_'93'__188 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_510 (coe v1))
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
                            (d_showPolyType_510 (coe v3)) (")" :: Data.Text.Text))))))
      C_PEff_190 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Eff " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_510 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text) (d_showPolyType_510 (coe v2))))
      C_Pμ'45'type_192 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\956 " :: Data.Text.Text) (d_showPolyFunctor_512 (coe v1))
      C_Pν'45'type_194 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("\957 " :: Data.Text.Text) (d_showPolyFunctor_512 (coe v1))
      C_PInt_196 -> coe ("Int" :: Data.Text.Text)
      C_PFloat_198 -> coe ("Float" :: Data.Text.Text)
      C_PStr_200 -> coe ("String" :: Data.Text.Text)
      C_PBuffer_202 -> coe ("Buffer" :: Data.Text.Text)
      C_PTVar_204 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.showPolyFunctor
d_showPolyFunctor_512 ::
  T_PolyFunctor_168 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunctor_512 v0
  = case coe v0 of
      C_PK_172 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(K " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyType_510 (coe v1)) (")" :: Data.Text.Text))
      C_PId_174 -> coe ("Id" :: Data.Text.Text)
      C__P'8853'__176 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_512 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8853 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_512 (coe v2)) (")" :: Data.Text.Text))))
      C__P'8855'__178 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showPolyFunctor_512 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \8855 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_showPolyFunctor_512 (coe v2)) (")" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.quantityEqBool
d_quantityEqBool_548 :: T_Quantity_4 -> T_Quantity_4 -> Bool
d_quantityEqBool_548 v0 v1
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
-- Once.Type.typeEqBool
d_typeEqBool_550 :: T_Type_38 -> T_Type_38 -> Bool
d_typeEqBool_550 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_Unit_48
           -> case coe v1 of
                C_Unit_48 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Void_50
           -> case coe v1 of
                C_Void_50 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'42'__52 v3 v4
           -> case coe v1 of
                C__'42'__52 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_550 (coe v3) (coe v5))
                       (coe d_typeEqBool_550 (coe v4) (coe v6))
                _ -> coe v2
         C__'43'__54 v3 v4
           -> case coe v1 of
                C__'43'__54 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_550 (coe v3) (coe v5))
                       (coe d_typeEqBool_550 (coe v4) (coe v6))
                _ -> coe v2
         C__'8658''91'_'93'__56 v3 v4 v5
           -> case coe v1 of
                C__'8658''91'_'93'__56 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_quantityEqBool_548 (coe v4) (coe v7))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe d_typeEqBool_550 (coe v3) (coe v6))
                          (coe d_typeEqBool_550 (coe v5) (coe v8)))
                _ -> coe v2
         C_Eff_58 v3 v4
           -> case coe v1 of
                C_Eff_58 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_typeEqBool_550 (coe v3) (coe v5))
                       (coe d_typeEqBool_550 (coe v4) (coe v6))
                _ -> coe v2
         C_μ'45'type_60 v3
           -> case coe v1 of
                C_μ'45'type_60 v4 -> coe d_functorEqBool_552 (coe v3) (coe v4)
                _ -> coe v2
         C_ν'45'type_62 v3
           -> case coe v1 of
                C_ν'45'type_62 v4 -> coe d_functorEqBool_552 (coe v3) (coe v4)
                _ -> coe v2
         C_Int_64
           -> case coe v1 of
                C_Int_64 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Float_66
           -> case coe v1 of
                C_Float_66 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Str_68
           -> case coe v1 of
                C_Str_68 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_Buffer_70
           -> case coe v1 of
                C_Buffer_70 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.functorEqBool
d_functorEqBool_552 :: T_Functor_36 -> T_Functor_36 -> Bool
d_functorEqBool_552 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_K_40 v3
           -> case coe v1 of
                C_K_40 v4 -> coe d_typeEqBool_550 (coe v3) (coe v4)
                _ -> coe v2
         C_Id_42
           -> case coe v1 of
                C_Id_42 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8853'__44 v3 v4
           -> case coe v1 of
                C__'8853'__44 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_552 (coe v3) (coe v5))
                       (coe d_functorEqBool_552 (coe v4) (coe v6))
                _ -> coe v2
         C__'8855'__46 v3 v4
           -> case coe v1 of
                C__'8855'__46 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_functorEqBool_552 (coe v3) (coe v5))
                       (coe d_functorEqBool_552 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Subst
d_Subst_618 :: ()
d_Subst_618 = erased
-- Once.Type._._×'_
d__'215'''__624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'215'''__624 = erased
-- Once.Type.lookupSubst
d_lookupSubst_626 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_Type_38
d_lookupSubst_626 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_626 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.extendSubst
d_extendSubst_660 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Type_38 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_660 v0 v1 v2
  = let v3 = d_lookupSubst_626 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_typeEqBool_550 (coe v1) (coe v4))
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
d_instantiate_690 ::
  T_PolyType_170 ->
  T_Type_38 -> Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_690 v0 v1
  = coe
      d_instantiateAcc_692 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.instantiateAcc
d_instantiateAcc_692 ::
  T_PolyType_170 ->
  T_Type_38 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_692 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PUnit_180
           -> case coe v1 of
                C_Unit_48 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PVoid_182
           -> case coe v1 of
                C_Void_50 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'42'__184 v4 v5
           -> case coe v1 of
                C__'42'__52 v6 v7
                  -> let v8 = d_instantiateAcc_692 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_692 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'43'__186 v4 v5
           -> case coe v1 of
                C__'43'__54 v6 v7
                  -> let v8 = d_instantiateAcc_692 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_692 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8658''91'_'93'__188 v4 v5 v6
           -> case coe v1 of
                C__'8658''91'_'93'__56 v7 v8 v9
                  -> let v10 = d_quantityEqBool_548 (coe v5) (coe v8) in
                     coe
                       (if coe v10
                          then let v11 = d_instantiateAcc_692 (coe v4) (coe v7) (coe v2) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                      -> coe d_instantiateAcc_692 (coe v6) (coe v9) (coe v12)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                _ -> coe v3
         C_PEff_190 v4 v5
           -> case coe v1 of
                C_Eff_58 v6 v7
                  -> let v8 = d_instantiateAcc_692 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateAcc_692 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C_Pμ'45'type_192 v4
           -> case coe v1 of
                C_μ'45'type_60 v5
                  -> coe d_instantiateFunctor_694 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_Pν'45'type_194 v4
           -> case coe v1 of
                C_ν'45'type_62 v5
                  -> coe d_instantiateFunctor_694 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PInt_196
           -> case coe v1 of
                C_Int_64 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PFloat_198
           -> case coe v1 of
                C_Float_66
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PStr_200
           -> case coe v1 of
                C_Str_68 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PBuffer_202
           -> case coe v1 of
                C_Buffer_70
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C_PTVar_204 v4 -> coe d_extendSubst_660 (coe v4) (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.instantiateFunctor
d_instantiateFunctor_694 ::
  T_PolyFunctor_168 ->
  T_Functor_36 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_694 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_PK_172 v4
           -> case coe v1 of
                C_K_40 v5 -> coe d_instantiateAcc_692 (coe v4) (coe v5) (coe v2)
                _ -> coe v3
         C_PId_174
           -> case coe v1 of
                C_Id_42 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         C__P'8853'__176 v4 v5
           -> case coe v1 of
                C__'8853'__44 v6 v7
                  -> let v8 = d_instantiateFunctor_694 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_694 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         C__P'8855'__178 v4 v5
           -> case coe v1 of
                C__'8855'__46 v6 v7
                  -> let v8 = d_instantiateFunctor_694 (coe v4) (coe v6) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe d_instantiateFunctor_694 (coe v5) (coe v7) (coe v9)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.applySubst
d_applySubst_998 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyType_170 -> Maybe T_Type_38
d_applySubst_998 v0 v1
  = case coe v1 of
      C_PUnit_180
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Unit_48)
      C_PVoid_182
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Void_50)
      C__P'42'__184 v2 v3
        -> let v4 = d_applySubst_998 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_998 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'42'__52 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'43'__186 v2 v3
        -> let v4 = d_applySubst_998 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_998 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'43'__54 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8658''91'_'93'__188 v2 v3 v4
        -> let v5 = d_applySubst_998 (coe v0) (coe v2) in
           coe
             (let v6 = d_applySubst_998 (coe v0) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8658''91'_'93'__56 (coe v7) (coe v3) (coe v8))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_PEff_190 v2 v3
        -> let v4 = d_applySubst_998 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubst_998 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C_Eff_58 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C_Pμ'45'type_192 v2
        -> let v3 = d_applySubstFunctor_1000 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_μ'45'type_60 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_Pν'45'type_194 v2
        -> let v3 = d_applySubstFunctor_1000 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_ν'45'type_62 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PInt_196
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Int_64)
      C_PFloat_198
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Float_66)
      C_PStr_200
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Str_68)
      C_PBuffer_202
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Buffer_70)
      C_PTVar_204 v2 -> coe d_lookupSubst_626 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.applySubstFunctor
d_applySubstFunctor_1000 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_PolyFunctor_168 -> Maybe T_Functor_36
d_applySubstFunctor_1000 v0 v1
  = case coe v1 of
      C_PK_172 v2
        -> let v3 = d_applySubst_998 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_K_40 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_PId_174
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_Id_42)
      C__P'8853'__176 v2 v3
        -> let v4 = d_applySubstFunctor_1000 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1000 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8853'__44 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      C__P'8855'__178 v2 v3
        -> let v4 = d_applySubstFunctor_1000 (coe v0) (coe v2) in
           coe
             (let v5 = d_applySubstFunctor_1000 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C__'8855'__46 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.schemaArrowCodomain
d_schemaArrowCodomain_1222 ::
  T_PolyType_170 -> T_Type_38 -> Maybe T_Type_38
d_schemaArrowCodomain_1222 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C__P'8658''91'_'93'__188 v3 v4 v5
           -> let v6
                    = d_instantiateAcc_692
                        (coe v3) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> coe d_applySubst_998 (coe v7) (coe v5)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
