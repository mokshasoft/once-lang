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
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Match.Subst
d_Subst_6 :: ()
d_Subst_6 = erased
-- Once.Type.Match.lookupSubst
d_lookupSubst_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst'45'aux_46 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_decide_42
             (coe
                MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v4))
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_62 v0 v1 v2
  = coe
      d_extendSubst'45'aux_46 (coe v0) (coe v1) (coe v2)
      (coe d_lookupSubst_8 (coe v0) (coe v2))
-- Once.Type.Match.maybe-bind
d_maybe'45'bind_74 ::
  () ->
  () -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'bind_74 ~v0 ~v1 v2 v3 = du_maybe'45'bind_74 v2 v3
du_maybe'45'bind_74 ::
  (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'bind_74 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.maybe-pair
d_maybe'45'pair_86 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_maybe'45'pair_86 ~v0 ~v1 ~v2 v3 v4 v5
  = du_maybe'45'pair_86 v3 v4 v5
du_maybe'45'pair_86 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_maybe'45'pair_86 v0 v1 v2
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
d_if'45'true'45'maybe_96 ::
  () -> Bool -> Maybe AgdaAny -> Maybe AgdaAny
d_if'45'true'45'maybe_96 ~v0 v1 v2
  = du_if'45'true'45'maybe_96 v1 v2
du_if'45'true'45'maybe_96 :: Bool -> Maybe AgdaAny -> Maybe AgdaAny
du_if'45'true'45'maybe_96 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Type.Match.instantiate
d_instantiate_100 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiate_100 v0 v1
  = coe
      d_instantiateAcc_102 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Type.Match.instantiateAcc
d_instantiateAcc_102 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateAcc_102 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_264
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PVoid_266
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'42'__268 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
               -> coe
                    du_maybe'45'bind_74 (coe d_instantiateAcc_102 (coe v4) (coe v6))
                    (coe d_instantiateAcc_102 (coe v3) (coe v5) (coe v2))
             MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'43'__270 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
               -> coe
                    du_maybe'45'bind_74 (coe d_instantiateAcc_102 (coe v4) (coe v6))
                    (coe d_instantiateAcc_102 (coe v3) (coe v5) (coe v2))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  du_decide_42
                                  (coe MAlonzo.Code.Once.Type.d__'8799'q__22 (coe v4) (coe v9))
                                  (coe
                                     du_maybe'45'bind_74
                                     (coe d_instantiateAcc_102 (coe v5) (coe v8))
                                     (coe d_instantiateAcc_102 (coe v3) (coe v6) (coe v2)))
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PEff_274 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> coe
                                         du_maybe'45'bind_74
                                         (coe d_instantiateAcc_102 (coe v4) (coe v7))
                                         (coe d_instantiateAcc_102 (coe v3) (coe v5) (coe v2))
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v4
               -> coe d_instantiateFunctor_104 (coe v3) (coe v4) (coe v2)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe d_instantiateFunctor_104 (coe v3) (coe v5) (coe v2)
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Unit_120
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Void_122
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Int_134
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Float_136
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_eff_36
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> coe d_instantiateFunctor_104 (coe v3) (coe v5) (coe v2)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Unit_120
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Void_122
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Int_134
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_Float_136
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PInt_280
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PFloat_282
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PTVar_284 v3
        -> coe d_extendSubst_62 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.instantiateFunctor
d_instantiateFunctor_104 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_instantiateFunctor_104 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_256 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_112 v4
               -> coe d_instantiateAcc_102 (coe v3) (coe v4) (coe v2)
             MAlonzo.Code.Once.Type.C_Id_114
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8853'__116 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8855'__118 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PId_258
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_112 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Id_114
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.Type.C__'8853'__116 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8855'__118 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8853'__260 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Id_114
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8853'__116 v5 v6
               -> coe
                    du_maybe'45'bind_74
                    (coe d_instantiateFunctor_104 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_104 (coe v3) (coe v5) (coe v2))
             MAlonzo.Code.Once.Type.C__'8855'__118 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8855'__262 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Id_114
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8853'__116 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'8855'__118 v5 v6
               -> coe
                    du_maybe'45'bind_74
                    (coe d_instantiateFunctor_104 (coe v4) (coe v6))
                    (coe d_instantiateFunctor_104 (coe v3) (coe v5) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.applySubst
d_applySubst_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_applySubst_214 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PUnit_264
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      MAlonzo.Code.Once.Type.C_PVoid_266
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Void_122)
      MAlonzo.Code.Once.Type.C__P'42'__268 v2 v3
        -> coe
             du_maybe'45'pair_86 (coe MAlonzo.Code.Once.Type.C__'42'__124)
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'43'__270 v2 v3
        -> coe
             du_maybe'45'pair_86 (coe MAlonzo.Code.Once.Type.C__'43'__126)
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v2 v3 v4
        -> coe
             du_maybe'45'pair_86
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                     (coe
                        MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v3)
                        (coe MAlonzo.Code.Once.Type.C_pure_34))))
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_PEff_274 v2 v3
        -> coe
             du_maybe'45'pair_86
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
                     (coe
                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_eff_36))))
             (coe d_applySubst_214 (coe v0) (coe v2))
             (coe d_applySubst_214 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v2
        -> coe
             du_maybe'45'bind_74
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v3))))
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v2 v3
        -> coe
             du_maybe'45'bind_74
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v4) (coe v3))))
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_PInt_280
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      MAlonzo.Code.Once.Type.C_PFloat_282
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      MAlonzo.Code.Once.Type.C_PTVar_284 v2
        -> coe d_lookupSubst_8 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.applySubstFunctor
d_applySubstFunctor_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Maybe MAlonzo.Code.Once.Type.T_Functor_106
d_applySubstFunctor_216 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PK_256 v2
        -> coe
             du_maybe'45'bind_74
             (coe
                (\ v3 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Once.Type.C_K_112 (coe v3))))
             (coe d_applySubst_214 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Id_114)
      MAlonzo.Code.Once.Type.C__P'8853'__260 v2 v3
        -> coe
             du_maybe'45'pair_86 (coe MAlonzo.Code.Once.Type.C__'8853'__116)
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe d_applySubstFunctor_216 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v2 v3
        -> coe
             du_maybe'45'pair_86 (coe MAlonzo.Code.Once.Type.C__'8855'__118)
             (coe d_applySubstFunctor_216 (coe v0) (coe v2))
             (coe d_applySubstFunctor_216 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Match.schemaArrowCodomain
d_schemaArrowCodomain_288 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_schemaArrowCodomain_288 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_264
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_PVoid_266
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__P'42'__268 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__P'43'__270 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v2 v3 v4
        -> coe
             du_maybe'45'bind_74
             (coe (\ v5 -> d_applySubst_214 (coe v5) (coe v4)))
             (coe d_instantiate_100 (coe v2) (coe v1))
      MAlonzo.Code.Once.Type.C_PEff_274 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_PInt_280
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_PFloat_282
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_PTVar_284 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
