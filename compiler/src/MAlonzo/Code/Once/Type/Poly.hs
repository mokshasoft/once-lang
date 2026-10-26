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

module MAlonzo.Code.Once.Type.Poly where

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
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Type.Poly.GroundF
d_GroundF_6 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 -> ()
d_GroundF_6 = erased
-- Once.Type.Poly.Ground
d_Ground_8 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 -> ()
d_Ground_8 = erased
-- Once.Type.Poly.extractGroundF
d_extractGroundF_48 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_extractGroundF_48 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_38
             (coe d_extractGround_54 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_Id_40
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8853'__42
                    (coe d_extractGroundF_48 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGroundF_48 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8855'__44
                    (coe d_extractGroundF_48 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGroundF_48 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.extractGround
d_extractGround_54 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_extractGround_54 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22
                    (coe d_extractGround_54 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGround_54 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24
                    (coe d_extractGround_54 (coe v0) (coe v3) (coe v5))
                    (coe d_extractGround_54 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_54 (coe v0) (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                    (coe d_extractGround_54 (coe v0) (coe v5) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_54 (coe v0) (coe v3) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                          (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                    (coe d_extractGround_54 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                    (coe d_extractGround_54 (coe v0) (coe v3) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                       (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
                    (coe d_extractGround_54 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ_28
             (coe d_extractGroundF_48 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν_30
             (coe d_extractGroundF_48 (coe v0) (coe v3) (coe v2)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.arrowPoly
d_arrowPoly_128 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_arrowPoly_128 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
                    (coe v2) (coe v1) (coe v3)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.polyOf
d_polyOf_148 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_polyOf_148 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
             (coe d_polyOf_148 (coe v1)) (coe d_polyOf_148 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30
             (coe d_polyOf_148 (coe v1)) (coe d_polyOf_148 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    d_arrowPoly_128 (coe v5) (coe v4) (coe d_polyOf_148 (coe v1))
                    (coe d_polyOf_148 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38
             (coe d_polyOfF_150 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40
             (coe d_polyOfF_150 (coe v1)) (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.polyOfF
d_polyOfF_150 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8
d_polyOfF_150 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12
             (coe d_polyOf_148 (coe v1))
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16
             (coe d_polyOfF_150 (coe v1)) (coe d_polyOfF_150 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18
             (coe d_polyOfF_150 (coe v1)) (coe d_polyOfF_150 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.substPoly
d_substPoly_186 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_substPoly_186 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ_28
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν_30
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.substPolyF
d_substPolyF_190 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_substPolyF_190 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_38
             (coe d_substPoly_186 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe MAlonzo.Code.Once.Spec.Type.C_Id_40
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v3))
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v3))
             (coe d_substPolyF_190 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.IsInstance
d_IsInstance_266 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_IsInstance_266 = erased
-- Once.Type.Poly.ftv
d_ftv_274 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftv_274 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_274 (coe v1)) (coe d_ftv_274 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_274 (coe v1)) (coe d_ftv_274 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_274 (coe v1)) (coe d_ftv_274 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_274 (coe v1)) (coe d_ftv_274 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftv_274 (coe v1)) (coe d_ftv_274 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v1
        -> coe d_ftvF_276 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v1 v2
        -> coe d_ftvF_276 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.ftvF
d_ftvF_276 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvF_276 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v1
        -> coe d_ftv_274 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_276 (coe v1)) (coe d_ftvF_276 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvF_276 (coe v1)) (coe d_ftvF_276 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Poly.ArrowSchema
d_ArrowSchema_314 a0 a1 a2 a3 = ()
data T_ArrowSchema_314
  = C_as'45'pure_320 | C_as'45'eff_326 | C_as'45'act_332
-- Once.Type.Poly.CodVarsInDom
d_CodVarsInDom_334 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 -> ()
d_CodVarsInDom_334 = erased
