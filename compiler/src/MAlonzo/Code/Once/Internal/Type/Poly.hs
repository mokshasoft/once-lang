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

module MAlonzo.Code.Once.Internal.Type.Poly where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Type.Poly.PolyFunctor
d_PolyFunctor_8 = ()
data T_PolyFunctor_8
  = C_PK_12 T_PolyType_10 | C_PId_14 |
    C__P'8853'__16 T_PolyFunctor_8 T_PolyFunctor_8 |
    C__P'8855'__18 T_PolyFunctor_8 T_PolyFunctor_8
-- Once.Internal.Type.Poly.PolyType
d_PolyType_10 = ()
data T_PolyType_10
  = C_PUnit_20 | C_PVoid_22 |
    C__P'42'__24 T_PolyType_10 T_PolyType_10 |
    C__P'43'__26 T_PolyType_10 T_PolyType_10 |
    C__P'8658''91'_'93'__28 T_PolyType_10
                            MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_PolyType_10 |
    C_PEff_30 T_PolyType_10 T_PolyType_10 |
    C_PAct_32 T_PolyType_10 T_PolyType_10 |
    C_Pμ'45'type_34 T_PolyFunctor_8 |
    C_Pν'45'type_36 T_PolyFunctor_8
                    MAlonzo.Code.Once.Spec.Grade.T_Finite_34 |
    C_PInt_38 | C_PFloat_40 |
    C_PTVar_42 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Internal.Type.Poly.GroundF
d_GroundF_44 :: T_PolyFunctor_8 -> ()
d_GroundF_44 = erased
-- Once.Internal.Type.Poly.Ground
d_Ground_46 :: T_PolyType_10 -> ()
d_Ground_46 = erased
-- Once.Internal.Type.Poly.extractGroundF
d_extractGroundF_86 ::
  Integer ->
  T_PolyFunctor_8 -> AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_extractGroundF_86 v0 v1 v2
  = case coe v1 of
      C_PK_12 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_38
             (coe d_extractGround_92 (coe v0) (coe v3) (coe v2))
      C_PId_14 -> coe MAlonzo.Code.Once.Spec.Type.C_Id_40
      C__P'8853'__16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8853'__42
                    (coe d_extractGroundF_86 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGroundF_86 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8855'__18 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8855'__44
                    (coe d_extractGroundF_86 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGroundF_86 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.extractGround
d_extractGround_92 ::
  Integer ->
  T_PolyType_10 -> AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_extractGround_92 v0 v1 v2
  = case coe v1 of
      C_PUnit_20 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      C_PVoid_22 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      C__P'42'__24 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22
                    (coe d_extractGround_92 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGround_92 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'43'__26 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24
                    (coe d_extractGround_92 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGround_92 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__P'8658''91'_'93'__28 v3 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_92 (coe v0) (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                    (coe d_extractGround_92 (coe v0) (coe v5) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PEff_30 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_92 (coe v0) (coe v3) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
                    (coe d_extractGround_92 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_PAct_32 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_92 (coe v0) (coe v3) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                    (coe d_extractGround_92 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Pμ'45'type_34 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ_28
             (coe d_extractGroundF_86 (coe v0) (coe v3) (coe v2))
      C_Pν'45'type_36 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν_30
             (coe d_extractGroundF_86 (coe v0) (coe v3) (coe v2)) (coe v4)
      C_PInt_38 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_PFloat_40 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.substPoly
d_substPoly_168 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_PolyType_10 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_substPoly_168 v0 v1 v2
  = case coe v2 of
      C_PUnit_20 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      C_PVoid_22 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      C__P'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v4))
      C__P'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v4))
      C__P'8658''91'_'93'__28 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v5))
      C_PEff_30 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v4))
      C_PAct_32 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v4))
      C_Pμ'45'type_34 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ_28
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v3))
      C_Pν'45'type_36 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν_30
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v3)) (coe v4)
      C_PInt_38 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_PFloat_40 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      C_PTVar_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.substPolyF
d_substPolyF_172 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  T_PolyFunctor_8 -> MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_substPolyF_172 v0 v1 v2
  = case coe v2 of
      C_PK_12 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_38
             (coe d_substPoly_168 (coe v0) (coe v1) (coe v3))
      C_PId_14 -> coe MAlonzo.Code.Once.Spec.Type.C_Id_40
      C__P'8853'__16 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v3))
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v4))
      C__P'8855'__18 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v3))
             (coe d_substPolyF_172 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.IsInstance
d_IsInstance_248 ::
  Integer ->
  T_PolyType_10 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_IsInstance_248 = erased
-- Once.Internal.Type.Poly.ftv
d_ftv_256 ::
  T_PolyType_10 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftv_256 v0
  = case coe v0 of
      C_PUnit_20 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PVoid_22 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_256 (coe v1)) (coe d_ftv_256 (coe v2))
      C__P'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_256 (coe v1)) (coe d_ftv_256 (coe v2))
      C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_256 (coe v1)) (coe d_ftv_256 (coe v3))
      C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_256 (coe v1)) (coe d_ftv_256 (coe v2))
      C_PAct_32 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_256 (coe v1)) (coe d_ftv_256 (coe v2))
      C_Pμ'45'type_34 v1 -> coe d_ftvF_258 (coe v1)
      C_Pν'45'type_36 v1 v2 -> coe d_ftvF_258 (coe v1)
      C_PInt_38 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PFloat_40 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_PTVar_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.ftvF
d_ftvF_258 ::
  T_PolyFunctor_8 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvF_258 v0
  = case coe v0 of
      C_PK_12 v1 -> coe d_ftv_256 (coe v1)
      C_PId_14 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_258 (coe v1)) (coe d_ftvF_258 (coe v2))
      C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_258 (coe v1)) (coe d_ftvF_258 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Type.Poly.ArrowSchema
d_ArrowSchema_296 a0 a1 a2 a3 = ()
data T_ArrowSchema_296
  = C_as'45'pure_302 | C_as'45'eff_308 | C_as'45'act_314
-- Once.Internal.Type.Poly.CodVarsInDom
d_CodVarsInDom_316 :: T_PolyType_10 -> T_PolyType_10 -> ()
d_CodVarsInDom_316 = erased
