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

module MAlonzo.Code.Once.Type.Instance where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Instance.ftvK
d_ftvK_6 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvK_6 v0
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
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v1
        -> coe d_ftvKF_8 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v1 v2
        -> coe d_ftvKF_8 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.ftvKF
d_ftvKF_8 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvKF_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v1
        -> coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_8 (coe v1)) (coe d_ftvKF_8 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_8 (coe v1)) (coe d_ftvKF_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.memberB
d_memberB_44 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_memberB_44 v0 v1
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
                       else coe seq (coe v6) (coe d_memberB_44 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.nubFrom
d_nubFrom_70 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nubFrom_70 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_memberB_44 (coe v2) (coe v0))
             (coe d_nubFrom_70 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe
                   d_nubFrom_70
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v0))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.nub
d_nub_80 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nub_80
  = coe
      d_nubFrom_70 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.Instance.params
d_params_82 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_params_82 v0
  = coe d_nub_80 (MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v0))
-- Once.Type.Instance.arityOf
d_arityOf_86 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 -> Integer
d_arityOf_86 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268 (d_params_82 (coe v0))
-- Once.Type.Instance.kindOf
d_kindOf_90 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70
d_kindOf_90 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_memberB_44 (coe v1) (coe d_ftvK_6 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Type.C_base_72)
      (coe MAlonzo.Code.Once.Spec.Type.C_any_74)
-- Once.Type.Instance.indexOf
d_indexOf_96 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Integer
d_indexOf_96 v0 v1
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
                              addInt (coe (1 :: Integer)) (coe d_indexOf_96 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.positionOf
d_positionOf_124 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_positionOf_124 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
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
                       then coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Data.Maybe.Base.du_map_64
                                 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
                                 (d_positionOf_124 (coe v0) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.rigidSubst
d_rigidSubst_152 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_rigidSubst_152 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
      (coe MAlonzo.Code.Once.Spec.Type.C_var_16)
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (d_positionOf_124 (coe v1) (coe d_params_82 (coe v0)))
-- Once.Type.Instance.rigidOf
d_rigidOf_160 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_rigidOf_160 v0
  = coe
      MAlonzo.Code.Once.Type.Poly.d_substPoly_186
      (coe d_arityOf_86 (coe v0)) (coe d_rigidSubst_152 (coe v0))
      (coe v0)
-- Once.Type.Instance.kindsOf
d_kindsOf_166 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70
d_kindsOf_166 v0 v1
  = coe
      d_kindOf_90 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe d_params_82 (coe v0)) (coe v1))
-- Once.Type.Instance.RespectsKinds
d_RespectsKinds_174 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  ()
d_RespectsKinds_174 = erased
-- Once.Type.Instance.KindedInstance
d_KindedInstance_186 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_KindedInstance_186 = erased
