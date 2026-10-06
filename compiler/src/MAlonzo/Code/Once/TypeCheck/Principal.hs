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

module MAlonzo.Code.Once.TypeCheck.Principal where

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
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Principal.isYes
d_isYes_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_isYes_10 ~v0 ~v1 v2 = du_isYes_10 v2
du_isYes_10 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_isYes_10 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.eqQuantity
d_eqQuantity_12 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> Bool
d_eqQuantity_12 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Zero_6
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Zero_6
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_One_8
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_One_8
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Many_10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Many_10
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.map2P
d_map2P_14 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.Type.T_PolyType_254) ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_map2P_14 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v4 v5)
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Principal.map2F
d_map2F_22 ::
  (MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
   MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
   MAlonzo.Code.Once.Type.T_PolyFunctor_252) ->
  Maybe MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyFunctor_252
d_map2F_22 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v4 v5)
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Principal.mv
d_mv_30 :: Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_mv_30 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("?" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Principal.PSubst
d_PSubst_34 :: ()
d_PSubst_34 = erased
-- Once.TypeCheck.Principal.lookupP
d_lookupP_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_lookupP_36 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupP_36 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.walk
d_walk_66 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
d_walk_66 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C_PTVar_284 v4
                  -> let v5 = d_lookupP_36 (coe v4) (coe v1) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe d_walk_66 (coe v3) (coe v1) (coe v6)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2)
-- Once.TypeCheck.Principal.zonk
d_zonk_96 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
d_zonk_96 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__P'42'__268 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C__P'42'__268
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Type.C__P'43'__270 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C__P'43'__270
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v4)) (coe v5)
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v6))
                MAlonzo.Code.Once.Type.C_PEff_274 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C_PEff_274
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v4
                  -> coe
                       MAlonzo.Code.Once.Type.C_Pμ'45'type_276
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v4))
                MAlonzo.Code.Once.Type.C_Pν'45'type_278 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C_Pν'45'type_278
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v4)) (coe v5)
                MAlonzo.Code.Once.Type.C_PTVar_284 v4
                  -> let v5 = d_lookupP_36 (coe v4) (coe v1) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe d_zonk_96 (coe v3) (coe v1) (coe v6)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2)
-- Once.TypeCheck.Principal.zonkF
d_zonkF_98 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252
d_zonkF_98 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C_PK_256 v4
                  -> coe
                       MAlonzo.Code.Once.Type.C_PK_256
                       (coe d_zonk_96 (coe v3) (coe v1) (coe v4))
                MAlonzo.Code.Once.Type.C_PId_258 -> coe v2
                MAlonzo.Code.Once.Type.C__P'8853'__260 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C__P'8853'__260
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v4))
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Type.C__P'8855'__262 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Type.C__P'8855'__262
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v4))
                       (coe d_zonkF_98 (coe v3) (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.occurs
d_occurs_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 -> Bool
d_occurs_200 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__P'42'__268 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Type.C__P'43'__270 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v5))
         MAlonzo.Code.Once.Type.C_PEff_274 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v3
           -> coe d_occursF_202 (coe v0) (coe v3)
         MAlonzo.Code.Once.Type.C_Pν'45'type_278 v3 v4
           -> coe d_occursF_202 (coe v0) (coe v3)
         MAlonzo.Code.Once.Type.C_PTVar_284 v3
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
                           (coe v3)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then coe seq (coe v6) (coe v5)
                          else coe seq (coe v6) (coe v5)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v2)
-- Once.TypeCheck.Principal.occursF
d_occursF_202 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 -> Bool
d_occursF_202 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PK_256 v2
        -> coe d_occurs_200 (coe v0) (coe v2)
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__P'8853'__260 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occursF_202 (coe v0) (coe v2))
             (coe d_occursF_202 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occursF_202 (coe v0) (coe v2))
             (coe d_occursF_202 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.bindVar
d_bindVar_268 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bindVar_268 v0 v1 v2 v3
  = coe
      du_go_282 (coe v1) (coe v3)
      (coe d_zonk_96 (coe v0) (coe v3) (coe v2))
-- Once.TypeCheck.Principal._.go
d_go_282 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_282 ~v0 v1 ~v2 v3 v4 = du_go_282 v1 v3 v4
du_go_282 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_282 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe d_occurs_200 (coe v0) (coe v2))
              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
              (coe
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v2))
                    (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C_PTVar_284 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                             (coe v0))
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                           (coe v4)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                     -> if coe v6
                          then coe
                                 seq (coe v7)
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
                          else coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                                          (coe v2))
                                       (coe v1)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.TypeCheck.Principal.unify
d_unify_296 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify_296 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_unify''_298 (coe v4) (coe v1)
                (coe d_walk_66 (coe v4) (coe v1) (coe v2))
                (coe d_walk_66 (coe v4) (coe v1) (coe v3)))
-- Once.TypeCheck.Principal.unify'
d_unify''_298 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify''_298 v0 v1 v2 v3
  = let v4
          = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v3 of
                 MAlonzo.Code.Once.Type.C_PTVar_284 v5
                   -> coe d_bindVar_268 (coe v0) (coe v5) (coe v2) (coe v1)
                 _ -> coe v4) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C_PUnit_264
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_PUnit_264
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_PTVar_284 v5
                  -> coe d_bindVar_268 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_PVoid_266
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_PVoid_266
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_PTVar_284 v5
                  -> coe d_bindVar_268 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C__P'42'__268 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C__P'42'__268 v7 v8
                  -> coe
                       d_unify2_300 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Type.C_PTVar_284 v7
                  -> coe d_bindVar_268 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C__P'43'__270 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C__P'43'__270 v7 v8
                  -> coe
                       d_unify2_300 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Type.C_PTVar_284 v7
                  -> coe d_bindVar_268 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v5 v6 v7
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe d_eqQuantity_12 (coe v6) (coe v9))
                       (coe
                          d_unify2_300 (coe v0) (coe v1) (coe v5) (coe v8) (coe v7)
                          (coe v10))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                MAlonzo.Code.Once.Type.C_PTVar_284 v8
                  -> coe d_bindVar_268 (coe v0) (coe v8) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_PEff_274 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_PEff_274 v7 v8
                  -> coe
                       d_unify2_300 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Type.C_PTVar_284 v7
                  -> coe d_bindVar_268 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v5
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v6
                  -> coe d_unifyF_302 (coe v0) (coe v1) (coe v5) (coe v6)
                MAlonzo.Code.Once.Type.C_PTVar_284 v6
                  -> coe d_bindVar_268 (coe v0) (coe v6) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_Pν'45'type_278 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_Pν'45'type_278 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe MAlonzo.Code.Once.Type.d_purityEqBool_482 (coe v6) (coe v8))
                       (coe d_unifyF_302 (coe v0) (coe v1) (coe v5) (coe v7))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                MAlonzo.Code.Once.Type.C_PTVar_284 v7
                  -> coe d_bindVar_268 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_PInt_280
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_PInt_280
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_PTVar_284 v5
                  -> coe d_bindVar_268 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_PFloat_282
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_PFloat_282
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Type.C_PTVar_284 v5
                  -> coe d_bindVar_268 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Type.C_PTVar_284 v5
           -> coe d_bindVar_268 (coe v0) (coe v5) (coe v3) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.unify2
d_unify2_300 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify2_300 v0 v1 v2 v3 v4 v5
  = let v6 = d_unify_296 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
           -> coe d_unify_296 (coe v0) (coe v7) (coe v4) (coe v5)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.unifyF
d_unifyF_302 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unifyF_302 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C_PK_256 v6
                     -> case coe v3 of
                          MAlonzo.Code.Once.Type.C_PK_256 v7
                            -> coe d_unify_296 (coe v4) (coe v1) (coe v6) (coe v7)
                          _ -> coe v5
                   MAlonzo.Code.Once.Type.C_PId_258
                     -> case coe v3 of
                          MAlonzo.Code.Once.Type.C_PId_258
                            -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                          _ -> coe v5
                   MAlonzo.Code.Once.Type.C__P'8853'__260 v6 v7
                     -> case coe v3 of
                          MAlonzo.Code.Once.Type.C__P'8853'__260 v8 v9
                            -> let v10 = d_unifyF_302 (coe v4) (coe v1) (coe v6) (coe v8) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe d_unifyF_302 (coe v4) (coe v11) (coe v7) (coe v9)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v5
                   MAlonzo.Code.Once.Type.C__P'8855'__262 v6 v7
                     -> case coe v3 of
                          MAlonzo.Code.Once.Type.C__P'8855'__262 v8 v9
                            -> let v10 = d_unifyF_302 (coe v4) (coe v1) (coe v6) (coe v8) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe d_unifyF_302 (coe v4) (coe v11) (coe v7) (coe v9)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v5
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Principal.typeToPoly
d_typeToPoly_552 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_typeToPoly_552 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_PUnit_264)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_PVoid_266)
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe
             d_map2P_14 (coe MAlonzo.Code.Once.Type.C__P'42'__268)
             (coe d_typeToPoly_552 (coe v1)) (coe d_typeToPoly_552 (coe v2))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe
             d_map2P_14 (coe MAlonzo.Code.Once.Type.C__P'43'__270)
             (coe d_typeToPoly_552 (coe v1)) (coe d_typeToPoly_552 (coe v2))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_pure_34
                      -> coe
                           d_map2P_14
                           (coe
                              (\ v6 ->
                                 coe
                                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 (coe v6)
                                   (coe v4)))
                           (coe d_typeToPoly_552 (coe v1)) (coe d_typeToPoly_552 (coe v3))
                    MAlonzo.Code.Once.Type.C_eff_36
                      -> let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                         coe
                           (case coe v4 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     d_map2P_14 (coe MAlonzo.Code.Once.Type.C_PEff_274)
                                     (coe d_typeToPoly_552 (coe v1)) (coe d_typeToPoly_552 (coe v3))
                              _ -> coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> let v2 = d_functorToPoly_554 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Pμ'45'type_276 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> let v3 = d_functorToPoly_554 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Pν'45'type_278 (coe v4) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_PInt_280)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_PFloat_282)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.functorToPoly
d_functorToPoly_554 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyFunctor_252
d_functorToPoly_554 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> let v2 = d_typeToPoly_552 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_PK_256 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_PId_258)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             d_map2F_22 (coe MAlonzo.Code.Once.Type.C__P'8853'__260)
             (coe d_functorToPoly_554 (coe v1))
             (coe d_functorToPoly_554 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             d_map2F_22 (coe MAlonzo.Code.Once.Type.C__P'8855'__262)
             (coe d_functorToPoly_554 (coe v1))
             (coe d_functorToPoly_554 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.builtinSchema
d_builtinSchema_632 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinSchema_632 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__268
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C_PTVar_284
                        (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("case" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe
                              MAlonzo.Code.Once.Type.C__P'43'__270
                              (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Type.C_PTVar_284
                                 (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe
                           MAlonzo.Code.Once.Type.C__P'42'__268
                           (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__268
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1))))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe MAlonzo.Code.Once.Type.C_PVoid_266)
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1))))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__P'43'__270
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C_PTVar_284
                        (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__P'43'__270
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1))))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                           (coe
                              MAlonzo.Code.Once.Type.C_PTVar_284
                              (coe d_mv_30 (coe addInt (coe (2 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe
                              MAlonzo.Code.Once.Type.C__P'42'__268
                              (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Type.C_PTVar_284
                                 (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe
                        MAlonzo.Code.Once.Type.C__P'42'__268
                        (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_PTVar_284
                           (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.C_PTVar_284
                        (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                     (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_PUnit_264))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Type.C_PUnit_264) (coe v1))
         _ -> coe v2)
-- Once.TypeCheck.Principal.lookupRen
d_lookupRen_658 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lookupRen_658 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupRen_658 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.freshen
d_freshen_688 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshen_688 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__P'42'__268 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'42'__268
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_688 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_688 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Type.C__P'43'__270 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'43'__270
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_688 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_688 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))
                   (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_688 (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_688 (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Type.C_PEff_274 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_PEff_274
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_688 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_688 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_688 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_688 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_Pμ'45'type_276
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF_690 (coe v4) (coe v1) (coe v2))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF_690 (coe v4) (coe v1) (coe v2)))
         MAlonzo.Code.Once.Type.C_Pν'45'type_278 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_Pν'45'type_278
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF_690 (coe v4) (coe v1) (coe v2)))
                   (coe v5))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF_690 (coe v4) (coe v1) (coe v2)))
         MAlonzo.Code.Once.Type.C_PTVar_284 v4
           -> let v5 = d_lookupRen_658 (coe v4) (coe v2) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v6))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                   (coe d_mv_30 (coe v1)))
                                (coe v2)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.TypeCheck.Principal.freshenF
d_freshenF_690 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshenF_690 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_256 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_PK_256
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshen_688 (coe v3) (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_freshen_688 (coe v3) (coe v1) (coe v2)))
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      MAlonzo.Code.Once.Type.C__P'8853'__260 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'8853'__260
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF_690 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF_690 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_690 (coe v3) (coe v1) (coe v2)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF_690 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'8855'__262
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF_690 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF_690 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_690 (coe v3) (coe v1) (coe v2)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF_690 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_690 (coe v3) (coe v1) (coe v2))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.Env
d_Env_886 :: ()
d_Env_886 = erased
-- Once.TypeCheck.Principal.lookupEnv
d_lookupEnv_888 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_lookupEnv_888 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupEnv_888 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.Result
d_Result_918 :: ()
d_Result_918 = erased
-- Once.TypeCheck.Principal.fuelD
d_fuelD_920 :: Integer
d_fuelD_920 = coe (500 :: Integer)
-- Once.TypeCheck.Principal._>>=R_
d__'62''62''61'R__922 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61'R__922 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.retTy
d_retTy_928 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_retTy_928 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.SchemaCtx
d_SchemaCtx_936 :: ()
d_SchemaCtx_936 = erased
-- Once.TypeCheck.Principal.projSchemas
d_projSchemas_938 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_projSchemas_938 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v5))
                           (coe d_projSchemas_938 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.lookupSchema
d_lookupSchema_946 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_lookupSchema_946 v0 v1
  = case coe v0 of
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
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupSchema_946 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.canonKey
d_canonKey_976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_canonKey_976 v0
  = case coe v0 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v1
        -> let v2
                 = MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v0) in
           coe
             (case coe v1 of
                (:) v3 v4
                  -> case coe v4 of
                       (:) v5 v6
                         -> case coe v6 of
                              []
                                -> let v7
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                             erased
                                             (\ v7 ->
                                                coe
                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                  (coe v3))
                                             (coe
                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.d_generatorNS_16)) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> if coe v8
                                               then coe seq (coe v9) (coe v5)
                                               else coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                                                         (coe v0))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.lookupName
d_lookupName_996 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupName_996 v0 v1 v2 v3
  = let v4 = d_builtinSchema_632 (coe v2) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v4
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v5 = d_lookupSchema_946 (coe v1) (coe v2) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_freshen_688 (coe v6) (coe v3)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_freshen_688 (coe v6) (coe v3)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v6
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_472
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> let v8 = d_typeToPoly_552 (coe v7) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) (coe v3))
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.liftName
d_liftName_1102 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftName_1102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.arrowParts
d_arrowParts_1110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowParts_1110 v0 v1 v2
  = coe
      du_go_1122 (coe v0) (coe v2)
      (coe d_walk_66 (coe d_fuelD_920) (coe v0) (coe v1))
-- Once.TypeCheck.Principal._.go
d_go_1122 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1122 v0 ~v1 v2 v3 = du_go_1122 v0 v2 v3
du_go_1122 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1122 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)))))
         MAlonzo.Code.Once.Type.C_PEff_274 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)))))
         MAlonzo.Code.Once.Type.C_PTVar_284 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                           (coe
                              d_occurs_200 (coe v4)
                              (let v5 = d_mv_30 (coe v1) in
                               coe
                                 (let v6 = d_lookupP_36 (coe d_mv_30 (coe v1)) (coe v0) in
                                  coe
                                    (let v7 = 498 :: Integer in
                                     coe
                                       (case coe v6 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                            -> coe d_zonk_96 (coe v7) (coe v0) (coe v8)
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v5)
                                          _ -> MAlonzo.RTE.mazUnreachableError)))))
                           (coe
                              d_occurs_200 (coe v4)
                              (coe
                                 d_zonk_96 (coe (499 :: Integer)) (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_PTVar_284
                                    (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))))
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                                    (let v5 = d_mv_30 (coe v1) in
                                     coe
                                       (let v6 = d_lookupP_36 (coe d_mv_30 (coe v1)) (coe v0) in
                                        coe
                                          (let v7 = 498 :: Integer in
                                           coe
                                             (case coe v6 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                  -> coe d_zonk_96 (coe v7) (coe v0) (coe v8)
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v5)
                                                _ -> MAlonzo.RTE.mazUnreachableError))))
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       d_zonk_96 (coe (499 :: Integer)) (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_PTVar_284
                                          (coe
                                             d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1)))))))
                              (coe v0))) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v1)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.Type.C_PTVar_284
                                   (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v1))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                      (coe addInt (coe (2 :: Integer)) (coe v1))))))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.TypeCheck.Principal.appFinish
d_appFinish_1144 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appFinish_1144 v0 v1 v2 v3
  = let v4
          = coe
              du_go_1122 (coe v3) (coe v2)
              (coe d_walk_66 (coe (500 :: Integer)) (coe v3) (coe v0)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v11 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> let v14
                                                = d_unify''_298
                                                    (coe (499 :: Integer)) (coe v12)
                                                    (coe
                                                       d_walk_66 (coe (499 :: Integer)) (coe v12)
                                                       (coe v6))
                                                    (coe
                                                       d_walk_66 (coe (499 :: Integer)) (coe v12)
                                                       (coe v1)) in
                                          coe
                                            (case coe v14 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_PEff_274
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_PUnit_264)
                                                               (coe v8))
                                                            (coe v8))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v13) (coe v15)))
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v14
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.composeFinish
d_composeFinish_1226 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_composeFinish_1226 v0 v1 v2 v3
  = let v4
          = coe
              du_go_1122 (coe v3) (coe v2)
              (coe d_walk_66 (coe (500 :: Integer)) (coe v3) (coe v0)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v11 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> let v14
                                                = coe
                                                    du_go_1122 (coe v12) (coe v13)
                                                    (coe
                                                       d_walk_66 (coe (500 :: Integer)) (coe v12)
                                                       (coe v1)) in
                                          coe
                                            (case coe v14 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                 -> case coe v15 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                        -> case coe v17 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                               -> case coe v19 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                      -> case coe v21 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                             -> let v24
                                                                                      = d_unify''_298
                                                                                          (coe
                                                                                             (499 ::
                                                                                                Integer))
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             d_walk_66
                                                                                             (coe
                                                                                                (499 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v22)
                                                                                             (coe
                                                                                                v18))
                                                                                          (coe
                                                                                             d_walk_66
                                                                                             (coe
                                                                                                (499 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v22)
                                                                                             (coe
                                                                                                v6)) in
                                                                                coe
                                                                                  (case coe v24 of
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                                                                                     (coe
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        v20))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Type.C_PEff_274
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        v8))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                     (coe
                                                                                                        v8)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v23)
                                                                                                  (coe
                                                                                                     v25)))
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                       -> coe v24
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v14
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.pInfer
d_pInfer_1378 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInfer_1378 v0 v1 v2 v3 v4 v5
  = let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
           -> let v8 = d_lookupEnv_888 (coe v7) (coe v2) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          d_liftName_1102
                          (coe d_lookupName_996 (coe v0) (coe v1) (coe v7) (coe v4)) (coe v5)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
           -> coe
                d_liftName_1102
                (coe
                   d_lookupName_996 (coe v0) (coe v1) (coe d_canonKey_976 (coe v7))
                   (coe v4))
                (coe v5)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v7 v8
           -> coe
                d_pInferApp_1380 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
                (coe v4) (coe v5)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v7 v8
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                         (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v4))))
                      (coe v2))
                   (coe v8) (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                (coe
                   (\ v9 ->
                      case coe v9 of
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                          -> coe
                               seq (coe v11)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                                        (coe
                                           MAlonzo.Code.Once.Type.C_PTVar_284
                                           (coe d_mv_30 (coe v4)))
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))
                                     (coe v11)))
                        _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v7 v8 v9
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda1_1494 (coe v0) (coe v1) (coe v2) (coe v7)
                   (coe v9))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v7 v8
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda2_1516 (coe v0) (coe v1) (coe v2) (coe v8))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v7 v8 v9 v10 v11
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda4_1552 (coe v0) (coe v1) (coe v2) (coe v8)
                   (coe v9) (coe v10) (coe v11))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Type.C_PUnit_264)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Type.C_PInt_280)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v7
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v7 v8
           -> let v9 = d_typeToPoly_552 (coe v8) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                     -> coe
                          d__'62''62''61'R__922
                          (coe
                             d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                             (coe v5))
                          (coe
                             (\ v11 ->
                                case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> case coe v13 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                           -> coe
                                                d_retTy_928 (coe v10) (coe v14)
                                                (coe
                                                   d_unify_296 (coe d_fuelD_920) (coe v15) (coe v12)
                                                   (coe v10))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v7 v8 v9
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda6_1662 (coe v0) (coe v1) (coe v2) (coe v7)
                   (coe v9))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v8
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   (\ v9 ->
                      case coe v9 of
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                          -> case coe v11 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                 -> coe
                                      d_retTy_928 (coe MAlonzo.Code.Once.Type.C_PInt_280) (coe v12)
                                      (coe
                                         d_unify_296 (coe d_fuelD_920) (coe v13) (coe v10)
                                         (coe MAlonzo.Code.Once.Type.C_PInt_280))
                               _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> coe v6)
-- Once.TypeCheck.Principal.pInferApp
d_pInferApp_1380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInferApp_1380 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_pAppGen_1384
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v10
                  -> coe
                       d_pInferAppB_1382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                       (coe v4) (coe v5) (coe v6)
                       (coe
                          du_isYes_10
                          (coe
                             MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116 (coe v10)
                             (coe
                                MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("Generators" :: Data.Text.Text))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe ("compose" :: Data.Text.Text))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                _ -> coe v7
         _ -> coe v7)
-- Once.TypeCheck.Principal.pInferAppB
d_pInferAppB_1382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInferAppB_1382 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             d__'62''62''61'R__922
             (coe
                d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                (coe v7))
             (coe
                du_'46'extendedlambda10_1750 (coe v0) (coe v1) (coe v2) (coe v5))
      else coe
             d_pAppGen_1384 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe v6) (coe v7)
-- Once.TypeCheck.Principal.pAppGen
d_pAppGen_1384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pAppGen_1384 v0 v1 v2 v3 v4 v5 v6
  = coe
      d__'62''62''61'R__922
      (coe
         d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
         (coe v6))
      (coe
         du_'46'extendedlambda12_1796 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.TypeCheck.Principal.destructFinish
d_destructFinish_1386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_destructFinish_1386 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = d_unify''_298
              (coe (499 :: Integer)) (coe v9)
              (coe d_walk_66 (coe (499 :: Integer)) (coe v9) (coe v7))
              (coe
                 d_walk_66 (coe (499 :: Integer)) (coe v9)
                 (coe
                    MAlonzo.Code.Once.Type.C__P'43'__270
                    (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Type.C_PTVar_284
                       (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v8)))))) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
           -> coe
                d__'62''62''61'R__922
                (coe
                   d_pInfer_1378 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                         (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe d_mv_30 (coe v8))))
                      (coe v2))
                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v8)) (coe v11))
                (coe
                   du_'46'extendedlambda14_1878 (coe v8) (coe v0) (coe v1) (coe v2)
                   (coe v5) (coe v6))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal..extendedlambda1
d_'46'extendedlambda1_1494 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda1_1494 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda1_1494 v0 v1 v2 v3 v5 v8
du_'46'extendedlambda1_1494 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda1_1494 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    d_pInfer_1378 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6))
                       (coe v2))
                    (coe v4) (coe v8) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda2
d_'46'extendedlambda2_1516 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda2_1516 v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_'46'extendedlambda2_1516 v0 v1 v2 v4 v7
du_'46'extendedlambda2_1516 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda2_1516 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
                    (coe
                       (\ v9 ->
                          case coe v9 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                              -> coe
                                   seq (coe v11)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Type.C__P'42'__268 (coe v5) (coe v10))
                                         (coe v11)))
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda4
d_'46'extendedlambda4_1552 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda4_1552 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10
  = du_'46'extendedlambda4_1552 v0 v1 v2 v4 v5 v6 v7 v10
du_'46'extendedlambda4_1552 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda4_1552 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    d_destructFinish_1386 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v8) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda6
d_'46'extendedlambda6_1662 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda6_1662 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda6_1662 v0 v1 v2 v3 v5 v8
du_'46'extendedlambda6_1662 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda6_1662 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_retTy_928 (coe MAlonzo.Code.Once.Type.C_PInt_280) (coe v8)
                       (coe
                          d_unify_296 (coe d_fuelD_920) (coe v9) (coe v6)
                          (coe MAlonzo.Code.Once.Type.C_PInt_280)))
                    (coe
                       du_'46'extendedlambda7_1670 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda7
d_'46'extendedlambda7_1670 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda7_1670 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10
                           v11
  = du_'46'extendedlambda7_1670 v0 v1 v2 v3 v5 v9 v11
du_'46'extendedlambda7_1670 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda7_1670 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                       (coe v10))
                    (coe
                       (\ v11 ->
                          case coe v11 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                              -> case coe v13 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                     -> coe
                                          d_retTy_928
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.d_isComparisonOp_92
                                                (coe v3))
                                             (coe
                                                MAlonzo.Code.Once.Type.C__P'43'__270
                                                (coe MAlonzo.Code.Once.Type.C_PUnit_264)
                                                (coe MAlonzo.Code.Once.Type.C_PUnit_264))
                                             (coe MAlonzo.Code.Once.Type.C_PInt_280))
                                          (coe v14)
                                          (coe
                                             d_unify_296 (coe d_fuelD_920) (coe v15) (coe v12)
                                             (coe MAlonzo.Code.Once.Type.C_PInt_280))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda10
d_'46'extendedlambda10_1750 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda10_1750 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda10_1750 v0 v1 v2 v5 v8
du_'46'extendedlambda10_1750 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda10_1750 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
                    (coe
                       (\ v9 ->
                          case coe v9 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                              -> case coe v11 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                     -> coe
                                          d_composeFinish_1226 (coe v5) (coe v10) (coe v12)
                                          (coe v13)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda12
d_'46'extendedlambda12_1796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda12_1796 v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_'46'extendedlambda12_1796 v0 v1 v2 v4 v7
du_'46'extendedlambda12_1796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda12_1796 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_pInfer_1378 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
                    (coe
                       (\ v9 ->
                          case coe v9 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                              -> case coe v11 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                     -> coe d_appFinish_1144 (coe v5) (coe v10) (coe v12) (coe v13)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda14
d_'46'extendedlambda14_1878 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda14_1878 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 v10
                            v11
  = du_'46'extendedlambda14_1878 v1 v4 v5 v6 v9 v10 v11
du_'46'extendedlambda14_1878 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda14_1878 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    d__'62''62''61'R__922
                    (coe
                       d_pInfer_1378 (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Type.C_PTVar_284
                                (coe d_mv_30 (coe addInt (coe (1 :: Integer)) (coe v0)))))
                          (coe v3))
                       (coe v5) (coe v9) (coe v10))
                    (coe
                       (\ v11 ->
                          case coe v11 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                              -> case coe v13 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                     -> coe
                                          d_retTy_928 (coe v7) (coe v14)
                                          (coe
                                             d_unify_296 (coe d_fuelD_920) (coe v15) (coe v7)
                                             (coe v12))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.renameVars
d_renameVars_1894 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
d_renameVars_1894 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_freshen''_1906 (coe v0) (coe v0) (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.TypeCheck.Principal._.letter
d_letter_1902 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_letter_1902 ~v0 v1 = du_letter_1902 v1
du_letter_1902 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_letter_1902 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("t" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Principal._.freshen'
d_freshen''_1906 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshen''_1906 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__P'42'__268 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'42'__268
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1906 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1906 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Type.C__P'43'__270 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'43'__270
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1906 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1906 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v5 v6 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1906 (coe v0) (coe v7)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1906 (coe v0) (coe v7)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Type.C_PEff_274 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_PEff_274
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1906 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1906 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1906 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_Pμ'45'type_276
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF''_1908 (coe v0) (coe v5) (coe v2) (coe v3))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF''_1908 (coe v0) (coe v5) (coe v2) (coe v3)))
         MAlonzo.Code.Once.Type.C_Pν'45'type_278 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Type.C_Pν'45'type_278
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF''_1908 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe v6))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF''_1908 (coe v0) (coe v5) (coe v2) (coe v3)))
         MAlonzo.Code.Once.Type.C_PTVar_284 v5
           -> let v6 = d_lookupRen_658 (coe v5) (coe v3) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Type.C_PTVar_284 (coe du_letter_1902 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v2))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                   (coe du_letter_1902 (coe v2)))
                                (coe v3)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v4)
-- Once.TypeCheck.Principal._.freshenF'
d_freshenF''_1908 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshenF''_1908 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PK_256 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_PK_256
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshen''_1906 (coe v0) (coe v4) (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_freshen''_1906 (coe v0) (coe v4) (coe v2) (coe v3)))
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
      MAlonzo.Code.Once.Type.C__P'8853'__260 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'8853'__260
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF''_1908 (coe v0) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF''_1908 (coe v0) (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__P'8855'__262
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF''_1908 (coe v0) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF''_1908 (coe v0) (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1908 (coe v0) (coe v4) (coe v2) (coe v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.groundOr
d_groundOr_2104 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_groundOr_2104 v0
  = let v1 = MAlonzo.Code.Once.Type.d_isGround_408 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                   (coe MAlonzo.Code.Once.Type.d_extractGround_326 (coe v0) (coe v2)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                   (coe d_renameVars_1894 (coe v0)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.finishP
d_finishP_2118 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_finishP_2118 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           d_groundOr_2104 (coe d_zonk_96 (coe d_fuelD_920) (coe v5) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.principal
d_principal_2124 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_principal_2124 v0 v1
  = coe
      d_finishP_2118
      (coe
         d_pInfer_1378
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v0))
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v0)))
         (coe
            d_projSchemas_938
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.TypeCheck.Principal.pgProj
d_pgProj_2130 ::
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_pgProj_2130 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.principalGround
d_principalGround_2134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_principalGround_2134 v0 v1
  = coe d_pgProj_2130 (coe d_principal_2124 (coe v0) (coe v1))
-- Once.TypeCheck.Principal.pgSchema
d_pgSchema_2140 ::
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_pgSchema_2140 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.siglessSchema
d_siglessSchema_2144 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_PolyType_254
d_siglessSchema_2144 v0
  = coe
      d_pgSchema_2140
      (coe
         d_principal_2124
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_410) (coe v0))
