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

module MAlonzo.Code.Once.Spec.Type.Poly where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade

-- Once.Spec.Type.Poly.PolyFunctor
d_PolyFunctor_8 = ()
data T_PolyFunctor_8
  = C_PK_12 T_PolyType_10 | C_PId_14 |
    C__P'8853'__16 T_PolyFunctor_8 T_PolyFunctor_8 |
    C__P'8855'__18 T_PolyFunctor_8 T_PolyFunctor_8
-- Once.Spec.Type.Poly.PolyType
d_PolyType_10 = ()
data T_PolyType_10
  = C_PUnit_20 | C_PVoid_22 |
    C__P'42'__24 T_PolyType_10 T_PolyType_10 |
    C__P'43'__26 T_PolyType_10 T_PolyType_10 |
    C__P'8658''91'_'93'__28 T_PolyType_10
                            MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 T_PolyType_10 |
    C_PEff_30 T_PolyType_10 T_PolyType_10 |
    C_Pμ'45'type_32 T_PolyFunctor_8 |
    C_Pν'45'type_34 T_PolyFunctor_8
                    MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 |
    C_PInt_36 | C_PFloat_38 |
    C_PTVar_40 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Spec.Type.Poly.GroundF
d_GroundF_42 :: T_PolyFunctor_8 -> ()
d_GroundF_42 = erased
-- Once.Spec.Type.Poly.Ground
d_Ground_44 :: T_PolyType_10 -> ()
d_Ground_44 = erased
-- Once.Spec.Type.Poly.extractGroundF
d_extractGroundF_78 ::
  T_PolyFunctor_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Functor_6
d_extractGroundF_78 v0 v1
  = case coe v0 of
      C_PK_12 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_12
             (coe d_extractGround_82 (coe v2) (coe v1))
      C_PId_14 -> coe MAlonzo.Code.Once.Spec.Type.C_Id_14
      C__P'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8853'__16
                    (coe d_extractGroundF_78 (coe v2) (coe v4))
                    (coe d_extractGroundF_78 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8855'__18
                    (coe d_extractGroundF_78 (coe v2) (coe v4))
                    (coe d_extractGroundF_78 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.extractGround
d_extractGround_82 ::
  T_PolyType_10 -> AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Type_8
d_extractGround_82 v0 v1
  = case coe v0 of
      C_PUnit_20 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_20
      C_PVoid_22 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_22
      C__P'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'42'__24
                    (coe d_extractGround_82 (coe v2) (coe v4))
                    (coe d_extractGround_82 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'43'__26
                    (coe d_extractGround_82 (coe v2) (coe v4))
                    (coe d_extractGround_82 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
                    (coe d_extractGround_82 (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 (coe v3)
                       (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
                    (coe d_extractGround_82 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_30 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
                    (coe d_extractGround_82 (coe v2) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                       (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
                    (coe d_extractGround_82 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_32 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30
             (coe d_extractGroundF_78 (coe v2) (coe v1))
      C_Pν'45'type_34 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32
             (coe d_extractGroundF_78 (coe v2) (coe v1)) (coe v3)
      C_PInt_36 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_34
      C_PFloat_38 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.substPoly
d_substPoly_148 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  T_PolyType_10 -> MAlonzo.Code.Once.Spec.Type.T_Type_8
d_substPoly_148 v0 v1
  = case coe v1 of
      C_PUnit_20 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_20
      C_PVoid_22 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_22
      C__P'42'__24 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__24
             (coe d_substPoly_148 (coe v0) (coe v2))
             (coe d_substPoly_148 (coe v0) (coe v3))
      C__P'43'__26 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__26
             (coe d_substPoly_148 (coe v0) (coe v2))
             (coe d_substPoly_148 (coe v0) (coe v3))
      C__P'8658''91'_'93'__28 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
             (coe d_substPoly_148 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
             (coe d_substPoly_148 (coe v0) (coe v4))
      C_PEff_30 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
             (coe d_substPoly_148 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
             (coe d_substPoly_148 (coe v0) (coe v3))
      C_Pμ'45'type_32 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30
             (coe d_substPolyF_150 (coe v0) (coe v2))
      C_Pν'45'type_34 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32
             (coe d_substPolyF_150 (coe v0) (coe v2)) (coe v3)
      C_PInt_36 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_34
      C_PFloat_38 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_36
      C_PTVar_40 v2 -> coe v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.substPolyF
d_substPolyF_150 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  T_PolyFunctor_8 -> MAlonzo.Code.Once.Spec.Type.T_Functor_6
d_substPolyF_150 v0 v1
  = case coe v1 of
      C_PK_12 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_12
             (coe d_substPoly_148 (coe v0) (coe v2))
      C_PId_14 -> coe MAlonzo.Code.Once.Spec.Type.C_Id_14
      C__P'8853'__16 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16
             (coe d_substPolyF_150 (coe v0) (coe v2))
             (coe d_substPolyF_150 (coe v0) (coe v3))
      C__P'8855'__18 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18
             (coe d_substPolyF_150 (coe v0) (coe v2))
             (coe d_substPolyF_150 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.IsInstance
d_IsInstance_218 ::
  T_PolyType_10 -> MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_IsInstance_218 = erased
-- Once.Spec.Type.Poly.ftv
d_ftv_226 ::
  T_PolyType_10 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftv_226 v0
  = case coe v0 of
      C_PUnit_20 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PVoid_22 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_226 (coe v1)) (coe d_ftv_226 (coe v2))
      C__P'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_226 (coe v1)) (coe d_ftv_226 (coe v2))
      C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_226 (coe v1)) (coe d_ftv_226 (coe v3))
      C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_226 (coe v1)) (coe d_ftv_226 (coe v2))
      C_Pμ'45'type_32 v1 -> coe d_ftvF_228 (coe v1)
      C_Pν'45'type_34 v1 v2 -> coe d_ftvF_228 (coe v1)
      C_PInt_36 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PFloat_38 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PTVar_40 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.ftvF
d_ftvF_228 ::
  T_PolyFunctor_8 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvF_228 v0
  = case coe v0 of
      C_PK_12 v1 -> coe d_ftv_226 (coe v1)
      C_PId_14 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_228 (coe v1)) (coe d_ftvF_228 (coe v2))
      C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_228 (coe v1)) (coe d_ftvF_228 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Poly.ArrowSchema
d_ArrowSchema_262 a0 a1 a2 a3 = ()
data T_ArrowSchema_262 = C_as'45'pure_268 | C_as'45'eff_274
-- Once.Spec.Type.Poly.CodVarsInDom
d_CodVarsInDom_276 :: T_PolyType_10 -> T_PolyType_10 -> ()
d_CodVarsInDom_276 = erased
