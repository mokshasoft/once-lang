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

module MAlonzo.Code.Once.Spec.Type.Instance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Spec.Type.Instance.ftvK
d_ftvK_8 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvK_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PUnit_20
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.Poly.C_PVoid_22
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_8 (coe v1)) (coe d_ftvK_8 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_8 (coe v1)) (coe d_ftvK_8 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_8 (coe v1)) (coe d_ftvK_8 (coe v3))
      MAlonzo.Code.Once.Spec.Type.Poly.C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_8 (coe v1)) (coe d_ftvK_8 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pμ'45'type_32 v1
        -> coe d_ftvKF_10 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pν'45'type_34 v1 v2
        -> coe d_ftvKF_10 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PInt_36
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.Poly.C_PFloat_38
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.Poly.C_PTVar_40 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Instance.ftvKF
d_ftvKF_10 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvKF_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PK_12 v1
        -> coe MAlonzo.Code.Once.Spec.Type.Poly.d_ftv_226 (coe v1)
      MAlonzo.Code.Once.Spec.Type.Poly.C_PId_14
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_10 (coe v1)) (coe d_ftvKF_10 (coe v2))
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_10 (coe v1)) (coe d_ftvKF_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Instance.memberB
d_memberB_42 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_memberB_42 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v5)
                       else coe seq (coe v6) (coe d_memberB_42 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Instance.nubFrom
d_nubFrom_68 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nubFrom_68 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_memberB_42 (coe v2) (coe v0))
             (coe d_nubFrom_68 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe
                   d_nubFrom_68
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v0))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Instance.nub
d_nub_78 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nub_78
  = coe
      d_nubFrom_68 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Spec.Type.Instance.params
d_params_80 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_params_80 v0
  = coe
      d_nub_78 (MAlonzo.Code.Once.Spec.Type.Poly.d_ftv_226 (coe v0))
-- Once.Spec.Type.Instance.arityOf
d_arityOf_84 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 -> Integer
d_arityOf_84 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268 (d_params_80 (coe v0))
-- Once.Spec.Type.Instance.kindOf
d_kindOf_88 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_TKind_10
d_kindOf_88 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_memberB_42 (coe v1) (coe d_ftvK_8 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Type.C_k'45'base_40)
      (coe MAlonzo.Code.Once.Spec.Type.C_k'45'any_42)
-- Once.Spec.Type.Instance.indexOf
d_indexOf_94 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Integer
d_indexOf_94 v0 v1
  = case coe v1 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe (0 :: Integer))
                       else coe
                              addInt (coe (1 :: Integer)) (coe d_indexOf_94 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Type.Instance.rigidSubst
d_rigidSubst_120 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_rigidSubst_120 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Type.C_rigid_38
      (coe d_kindOf_88 (coe v0) (coe v1))
      (coe d_indexOf_94 (coe v1) (coe d_params_80 (coe v0)))
-- Once.Spec.Type.Instance.rigidOf
d_rigidOf_126 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_rigidOf_126 v0
  = coe
      MAlonzo.Code.Once.Spec.Type.Poly.d_substPoly_148
      (coe d_rigidSubst_120 (coe v0)) (coe v0)
-- Once.Spec.Type.Instance.RespectsKinds
d_RespectsKinds_130 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  ()
d_RespectsKinds_130 = erased
-- Once.Spec.Type.Instance.KindedInstance
d_KindedInstance_138 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_KindedInstance_138 = erased
