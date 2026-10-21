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

module MAlonzo.Code.Once.Type.Match where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Match.Subst
d_Subst_6 :: ()
d_Subst_6 = erased
-- Once.Type.Match.lookupSubst
d_lookupSubst_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8
d_lookupSubst_8 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSubst_8 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.decide
d_decide_42 ::
  () ->
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny -> Maybe AgdaAny
d_decide_42 ~v0 ~v1 v2 v3 = du_decide_42 v2 v3
du_decide_42 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny -> Maybe AgdaAny
du_decide_42 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe seq (coe v3) (coe v1)
             else coe
                    seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.extendSubst-aux
d_extendSubst'45'aux_46 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst'45'aux_46 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_decide_42
             (coe
                MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216 (coe v1)
                (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.extendSubst
d_extendSubst_62 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_62 v0 v1 v2
  = coe
      d_extendSubst'45'aux_46 (coe v0) (coe v1) (coe v2)
      (coe d_lookupSubst_8 (coe v0) (coe v2))
-- Once.Type.Match.maybe-pair
d_maybe'45'pair_76 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'pair_76 ~v0 ~v1 ~v2 v3 v4 v5
  = du_maybe'45'pair_76 v3 v4 v5
du_maybe'45'pair_76 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'pair_76 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.if-true-maybe
d_if'45'true'45'maybe_86 ::
  () -> Bool -> Maybe AgdaAny -> Maybe AgdaAny
d_if'45'true'45'maybe_86 ~v0 v1 v2
  = du_if'45'true'45'maybe_86 v1 v2
du_if'45'true'45'maybe_86 :: Bool -> Maybe AgdaAny -> Maybe AgdaAny
du_if'45'true'45'maybe_86 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Type.Match.instantiate
d_instantiate_90 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_90 v0 v1
  = coe
      d_instantiateAcc_92 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.Match.instantiateAcc
d_instantiateAcc_92 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_92 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.Poly.C_PUnit_20
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PVoid_22
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'42'__24 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe d_instantiateAcc_92 (coe v3) (coe v5) (coe v2))
                    (coe d_instantiateAcc_92 (coe v4) (coe v6))
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'43'__26 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe d_instantiateAcc_92 (coe v3) (coe v5) (coe v2))
                    (coe d_instantiateAcc_92 (coe v4) (coe v6))
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8658''91'_'93'__28 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                    -> coe
                                         du_decide_42
                                         (coe
                                            MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'q__8
                                            (coe v4) (coe v9))
                                         (coe
                                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                            (coe d_instantiateAcc_92 (coe v3) (coe v6) (coe v2))
                                            (coe d_instantiateAcc_92 (coe v5) (coe v8)))
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PEff_30 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v8 v9
                      -> let v10
                               = case coe v9 of
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v10
                                     -> coe
                                          seq (coe v10)
                                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                   _ -> MAlonzo.RTE.mazUnreachableError in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Spec.Grade.C_fin_42 v11
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            _ -> coe v10
                                     MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_One_10
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Spec.Grade.C_fin_42 v11
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            _ -> coe v10
                                     MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Spec.Grade.C_fin_42 v11
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            _ -> coe v10
                                     MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                       -> coe
                                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                            (coe d_instantiateAcc_92 (coe v3) (coe v5) (coe v2))
                                            (coe d_instantiateAcc_92 (coe v4) (coe v7))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PAct_32 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v10
                                    -> coe
                                         seq (coe v10)
                                         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v10
                                    -> coe
                                         seq (coe v10)
                                         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v10
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                           -> coe
                                                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                                (coe d_instantiateAcc_92 (coe v3) (coe v5) (coe v2))
                                                (coe d_instantiateAcc_92 (coe v4) (coe v7))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pμ'45'type_34 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v4
               -> coe d_instantiateFunctor_94 (coe v3) (coe v4) (coe v2)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pν'45'type_36 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe d_instantiateFunctor_94 (coe v3) (coe v5) (coe v2)
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Internal.Type.C_Unit_20
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Void_22
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Int_34
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Float_36
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe d_instantiateFunctor_94 (coe v3) (coe v5) (coe v2)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Internal.Type.C_Unit_20
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Void_22
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Int_34
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_Float_36
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PInt_38
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PFloat_40
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PTVar_42 v3
        -> coe d_extendSubst_62 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.instantiateFunctor
d_instantiateFunctor_94 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_94 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.Poly.C_PK_12 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v4
               -> coe d_instantiateAcc_92 (coe v3) (coe v4) (coe v2)
             MAlonzo.Code.Once.Internal.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C_PId_14
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8853'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v5 v6
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe d_instantiateFunctor_94 (coe v3) (coe v5) (coe v2))
                    (coe d_instantiateFunctor_94 (coe v4) (coe v6))
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8855'__18 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Id_14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v5 v6
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe d_instantiateFunctor_94 (coe v3) (coe v5) (coe v2))
                    (coe d_instantiateFunctor_94 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.applySubst
d_applySubst_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8
d_applySubst_214 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.Poly.C_PUnit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
      MAlonzo.Code.Once.Internal.Type.Poly.C_PVoid_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Type.C_Void_22)
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'42'__24 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24)
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'43'__26 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe MAlonzo.Code.Once.Internal.Type.C__'43'__26)
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8658''91'_'93'__28 v2 v3 v4
        -> coe
             du_maybe'45'pair_76
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v5)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42
                           (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))))
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v4))
      MAlonzo.Code.Once.Internal.Type.Poly.C_PEff_30 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))))
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Type.Poly.C_PAct_32 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42
                           (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))))
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pμ'45'type_34 v2
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v3))))
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pν'45'type_36 v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v4) (coe v3))))
      MAlonzo.Code.Once.Internal.Type.Poly.C_PInt_38
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
      MAlonzo.Code.Once.Internal.Type.Poly.C_PFloat_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
      MAlonzo.Code.Once.Internal.Type.Poly.C_PTVar_42 v2
        -> coe d_lookupSubst_8 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.applySubstFunctor
d_applySubstFunctor_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyFunctor_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Functor_6
d_applySubstFunctor_216 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.Poly.C_PK_12 v2
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Internal.Type.C_K_12 (coe v3))))
      MAlonzo.Code.Once.Internal.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Internal.Type.C_Id_14)
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8853'__16 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe MAlonzo.Code.Once.Internal.Type.C__'8853'__16)
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe d_applySubstFunctor_216 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8855'__18 v2 v3
        -> coe
             du_maybe'45'pair_76
             (coe MAlonzo.Code.Once.Internal.Type.C__'8855'__18)
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe d_applySubstFunctor_216 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.schemaArrowCodomain
d_schemaArrowCodomain_298 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8
d_schemaArrowCodomain_298 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.Poly.C_PUnit_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_PVoid_22
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'42'__24 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'43'__26 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C__P'8658''91'_'93'__28 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_instantiate_90 (coe v2) (coe v1))
             (coe (\ v5 -> d_applySubst_214 (coe v5) (coe v4)))
      MAlonzo.Code.Once.Internal.Type.Poly.C_PEff_30 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_PAct_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pμ'45'type_34 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_Pν'45'type_36 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_PInt_38
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_PFloat_40
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Internal.Type.Poly.C_PTVar_42 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
