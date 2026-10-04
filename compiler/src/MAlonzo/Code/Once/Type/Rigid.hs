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

module MAlonzo.Code.Once.Type.Rigid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Type.Rigid.ftvK
d_ftvK_6 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvK_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_264
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_PVoid_266
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C__P'42'__268 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Type.C__P'43'__270 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v3))
      MAlonzo.Code.Once.Type.C_PEff_274 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvK_6 (coe v1)) (coe d_ftvK_6 (coe v2))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v1
        -> coe d_ftvKF_8 (coe v1)
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v1 v2
        -> coe d_ftvKF_8 (coe v1)
      MAlonzo.Code.Once.Type.C_PInt_280
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_PFloat_282
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_PTVar_284 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.ftvKF
d_ftvKF_8 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ftvKF_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_256 v1
        -> coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v1)
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C__P'8853'__260 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_8 (coe v1)) (coe d_ftvKF_8 (coe v2))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ftvKF_8 (coe v1)) (coe d_ftvKF_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.memberB
d_memberB_40 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_memberB_40 v0 v1
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
                       else coe seq (coe v6) (coe d_memberB_40 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.nubFrom
d_nubFrom_66 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nubFrom_66 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_memberB_40 (coe v2) (coe v0))
             (coe d_nubFrom_66 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe
                   d_nubFrom_66
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v0))
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.nub
d_nub_76 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nub_76
  = coe
      d_nubFrom_66 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.Rigid.params
d_params_78 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_params_78 v0
  = coe d_nub_76 (MAlonzo.Code.Once.Type.d_ftv_632 (coe v0))
-- Once.Type.Rigid.arityOf
d_arityOf_82 :: MAlonzo.Code.Once.Type.T_PolyType_254 -> Integer
d_arityOf_82 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268 (d_params_78 (coe v0))
-- Once.Type.Rigid.kindOf
d_kindOf_86 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_TKind_110
d_kindOf_86 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_memberB_40 (coe v1) (coe d_ftvK_6 (coe v0)))
      (coe MAlonzo.Code.Once.Type.C_k'45'base_140)
      (coe MAlonzo.Code.Once.Type.C_k'45'any_142)
-- Once.Type.Rigid.indexOf
d_indexOf_92 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Integer
d_indexOf_92 v0 v1
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
                              addInt (coe (1 :: Integer)) (coe d_indexOf_92 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidSubst
d_rigidSubst_118 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_rigidSubst_118 v0 v1
  = coe
      MAlonzo.Code.Once.Type.C_rigid_138
      (coe d_kindOf_86 (coe v0) (coe v1))
      (coe d_indexOf_92 (coe v1) (coe d_params_78 (coe v0)))
-- Once.Type.Rigid.rigidOf
d_rigidOf_124 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_rigidOf_124 v0
  = coe
      MAlonzo.Code.Once.Type.d_substPoly_562
      (coe d_rigidSubst_118 (coe v0)) (coe v0)
-- Once.Type.Rigid.RespectsKinds
d_RespectsKinds_128 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  ()
d_RespectsKinds_128 = erased
-- Once.Type.Rigid.KindedInstance
d_KindedInstance_136 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_KindedInstance_136 = erased
-- Once.Type.Rigid.subst-ground
d_subst'45'ground_150 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ground_150 = erased
-- Once.Type.Rigid.subst-groundF
d_subst'45'groundF_158 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'groundF_158 = erased
-- Once.Type.Rigid.++-⊥
d_'43''43''45''8869'_270 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''43''45''8869'_270 = erased
-- Once.Type.Rigid.ftv-ground
d_ftv'45'ground_314 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftv'45'ground_314 = erased
-- Once.Type.Rigid.ftvF-ground
d_ftvF'45'ground_320 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvF'45'ground_320 = erased
-- Once.Type.Rigid.ftvK-ground
d_ftvK'45'ground_386 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvK'45'ground_386 = erased
-- Once.Type.Rigid.ftvKF-ground
d_ftvKF'45'ground_392 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvKF'45'ground_392 = erased
-- Once.Type.Rigid.ground-kinded
d_ground'45'kinded_458 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground'45'kinded_458 ~v0 ~v1 = du_ground'45'kinded_458
du_ground'45'kinded_458 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ground'45'kinded_458
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 -> coe MAlonzo.Code.Once.Type.C_Unit_120))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            (\ v0 v1 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
-- Once.Type.Rigid.ftvK⊆ftv
d_ftvK'8838'ftv_472 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvK'8838'ftv_472 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C__P'42'__268 v3 v4
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v4))
             (coe d_ftvK'8838'ftv_472 (coe v3))
             (coe d_ftvK'8838'ftv_472 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Type.C__P'43'__270 v3 v4
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v4))
             (coe d_ftvK'8838'ftv_472 (coe v3))
             (coe d_ftvK'8838'ftv_472 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v3 v4 v5
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v5))
             (coe d_ftvK'8838'ftv_472 (coe v3))
             (coe d_ftvK'8838'ftv_472 (coe v5)) (coe v2)
      MAlonzo.Code.Once.Type.C_PEff_274 v3 v4
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v4))
             (coe d_ftvK'8838'ftv_472 (coe v3))
             (coe d_ftvK'8838'ftv_472 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v3
        -> coe d_ftvKF'8838'ftvF_478 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v3 v4
        -> coe d_ftvKF'8838'ftvF_478 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.ftvKF⊆ftvF
d_ftvKF'8838'ftvF_478 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvKF'8838'ftvF_478 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_256 v3 -> coe v2
      MAlonzo.Code.Once.Type.C__P'8853'__260 v3 v4
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvKF_8 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftvF_634 (coe v4))
             (coe d_ftvKF'8838'ftvF_478 (coe v3))
             (coe d_ftvKF'8838'ftvF_478 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Type.C__P'8855'__262 v3 v4
        -> coe
             du_'43''43''45'mono_494 (coe v1) (coe d_ftvKF_8 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3))
             (coe MAlonzo.Code.Once.Type.d_ftvF_634 (coe v4))
             (coe d_ftvKF'8838'ftvF_478 (coe v3))
             (coe d_ftvKF'8838'ftvF_478 (coe v4)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.++-mono
d_'43''43''45'mono_494 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'43''43''45'mono_494 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_'43''43''45'mono_494 v0 v1 v2 v4 v5 v6 v7
du_'43''43''45'mono_494 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'43''43''45'mono_494 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_'43''43''8315'_868
              (coe v1) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
           -> coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                v2 (coe v4 v0 v8)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                v2 v3 (coe v5 v0 v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Rigid.AllBase
d_AllBase_582 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_AllBase_582 = erased
-- Once.Type.Rigid.allBase?
d_allBase'63'_594 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allBase'63'_594 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                     (coe v0 v2) in
           coe
             (let v5 = d_allBase'63'_594 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                          -> coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v7)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  (coe
                                                     (\ v10 v11 ->
                                                        case coe v11 of
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v14
                                                            -> coe v6
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v14
                                                            -> coe v9 v10 v14
                                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v7)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid._.nothing≢just
d_nothing'8802'just_650 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_650 = erased
-- Once.Type.Rigid.kindedInstance?
d_kindedInstance'63'_658 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_kindedInstance'63'_658 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.Match.d_instantiateAcc_102
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> let v4 = MAlonzo.Code.Once.Type.Instance.d_θof_478 (coe v3) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_inst'45'sound_798 (coe v0)
                              (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe v3))
                           v3 erased in
                 coe
                   (let v6 = d_allBase'63'_594 (coe v4) (coe d_ftvK_6 (coe v0)) in
                    coe
                      (case coe v6 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                           -> if coe v7
                                then case coe v8 of
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                         -> coe
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v5) (coe v9))))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                else coe
                                       seq (coe v8)
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                          (coe v7)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                         _ -> MAlonzo.RTE.mazUnreachableError)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Rigid._.absurd
d_absurd_680 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_absurd_680 = erased
-- Once.Type.Rigid.RigidFree
d_RigidFree_748 a0 = ()
data T_RigidFree_748
  = C_rf'45'Unit_752 | C_rf'45'Void_754 | C_rf'45'Int_756 |
    C_rf'45'Float_758 |
    C_rf'45''42'_764 T_RigidFree_748 T_RigidFree_748 |
    C_rf'45''43'_770 T_RigidFree_748 T_RigidFree_748 |
    C_rf'45''8658'_778 T_RigidFree_748 T_RigidFree_748 |
    C_rf'45'μ_782 T_RigidFreeF_750 | C_rf'45'ν_788 T_RigidFreeF_750
-- Once.Type.Rigid.RigidFreeF
d_RigidFreeF_750 a0 = ()
data T_RigidFreeF_750
  = C_rf'45'K_792 T_RigidFree_748 | C_rf'45'Id_794 |
    C_rf'45''8853'_800 T_RigidFreeF_750 T_RigidFreeF_750 |
    C_rf'45''8855'_806 T_RigidFreeF_750 T_RigidFreeF_750
-- Once.Type.Rigid.both
d_both_814 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_both_814 ~v0 ~v1 ~v2 v3 v4 v5 = du_both_814 v3 v4 v5
du_both_814 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_both_814 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v4 v5)
                _ -> coe v3
         _ -> coe v3)
-- Once.Type.Rigid.one
d_one_828 ::
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_one_828 ~v0 ~v1 v2 v3 = du_one_828 v2 v3
du_one_828 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_one_828 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFree?
d_rigidFree'63'_838 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe T_RigidFree_748
d_rigidFree'63'_838 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_rf'45'Unit_752)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_rf'45'Void_754)
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             du_both_814 (coe C_rf'45''42'_764)
             (coe d_rigidFree'63'_838 (coe v1))
             (coe d_rigidFree'63'_838 (coe v2))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             du_both_814 (coe C_rf'45''43'_770)
             (coe d_rigidFree'63'_838 (coe v1))
             (coe d_rigidFree'63'_838 (coe v2))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe
             du_both_814 (coe C_rf'45''8658'_778)
             (coe d_rigidFree'63'_838 (coe v1))
             (coe d_rigidFree'63'_838 (coe v3))
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe
             du_one_828 (coe C_rf'45'μ_782) (coe d_rigidFreeF'63'_842 (coe v1))
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe
             du_one_828 (coe C_rf'45'ν_788) (coe d_rigidFreeF'63'_842 (coe v1))
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_rf'45'Int_756)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_rf'45'Float_758)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFreeF?
d_rigidFreeF'63'_842 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Maybe T_RigidFreeF_750
d_rigidFreeF'63'_842 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> coe
             du_one_828 (coe C_rf'45'K_792) (coe d_rigidFree'63'_838 (coe v1))
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_rf'45'Id_794)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             du_both_814 (coe C_rf'45''8853'_800)
             (coe d_rigidFreeF'63'_842 (coe v1))
             (coe d_rigidFreeF'63'_842 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             du_both_814 (coe C_rf'45''8855'_806)
             (coe d_rigidFreeF'63'_842 (coe v1))
             (coe d_rigidFreeF'63'_842 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFree?-complete
d_rigidFree'63''45'complete_878 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_RigidFree_748 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rigidFree'63''45'complete_878 = erased
-- Once.Type.Rigid.rigidFreeF?-complete
d_rigidFreeF'63''45'complete_884 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  T_RigidFreeF_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rigidFreeF'63''45'complete_884 = erased
-- Once.Type.Rigid.extractGround-rf
d_extractGround'45'rf_968 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 -> AgdaAny -> T_RigidFree_748
d_extractGround'45'rf_968 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_264 -> coe C_rf'45'Unit_752
      MAlonzo.Code.Once.Type.C_PVoid_266 -> coe C_rf'45'Void_754
      MAlonzo.Code.Once.Type.C__P'42'__268 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_rf'45''42'_764 (d_extractGround'45'rf_968 (coe v2) (coe v4))
                    (d_extractGround'45'rf_968 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'43'__270 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_rf'45''43'_770 (d_extractGround'45'rf_968 (coe v2) (coe v4))
                    (d_extractGround'45'rf_968 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    C_rf'45''8658'_778 (d_extractGround'45'rf_968 (coe v2) (coe v5))
                    (d_extractGround'45'rf_968 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PEff_274 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_rf'45''8658'_778 (d_extractGround'45'rf_968 (coe v2) (coe v4))
                    (d_extractGround'45'rf_968 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v2
        -> coe C_rf'45'μ_782 (d_extractGroundF'45'rf_974 (coe v2) (coe v1))
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v2 v3
        -> coe C_rf'45'ν_788 (d_extractGroundF'45'rf_974 (coe v2) (coe v1))
      MAlonzo.Code.Once.Type.C_PInt_280 -> coe C_rf'45'Int_756
      MAlonzo.Code.Once.Type.C_PFloat_282 -> coe C_rf'45'Float_758
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.extractGroundF-rf
d_extractGroundF'45'rf_974 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  AgdaAny -> T_RigidFreeF_750
d_extractGroundF'45'rf_974 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_256 v2
        -> coe C_rf'45'K_792 (d_extractGround'45'rf_968 (coe v2) (coe v1))
      MAlonzo.Code.Once.Type.C_PId_258 -> coe C_rf'45'Id_794
      MAlonzo.Code.Once.Type.C__P'8853'__260 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_rf'45''8853'_800 (d_extractGroundF'45'rf_974 (coe v2) (coe v4))
                    (d_extractGroundF'45'rf_974 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8855'__262 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_rf'45''8855'_806 (d_extractGroundF'45'rf_974 (coe v2) (coe v4))
                    (d_extractGroundF'45'rf_974 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
