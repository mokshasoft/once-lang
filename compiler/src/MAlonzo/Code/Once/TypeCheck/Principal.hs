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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Principal.map2P
d_map2P_6 ::
  (MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10) ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_map2P_6 v0 v1 v2
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
d_map2F_14 ::
  (MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8) ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8
d_map2F_14 v0 v1 v2
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
d_mv_22 :: Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_mv_22 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("?" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Principal.PSubst
d_PSubst_26 :: ()
d_PSubst_26 = erased
-- Once.TypeCheck.Principal.lookupP
d_lookupP_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_lookupP_28 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupP_28 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.walk
d_walk_58 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_walk_58 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
                  -> let v5 = d_lookupP_28 (coe v4) (coe v1) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe d_walk_58 (coe v3) (coe v1) (coe v6)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2)
-- Once.TypeCheck.Principal.zonk
d_zonk_88 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_zonk_88 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4)) (coe v5)
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v6))
                MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4))
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v4
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v4))
                MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v4)) (coe v5)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
                  -> let v5 = d_lookupP_28 (coe v4) (coe v1) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe d_zonk_88 (coe v3) (coe v1) (coe v6)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2)
-- Once.TypeCheck.Principal.zonkF
d_zonkF_90 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8
d_zonkF_90 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v4
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12
                       (coe d_zonk_88 (coe v3) (coe v1) (coe v4))
                MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14 -> coe v2
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v4))
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v5))
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v4 v5
                  -> coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v4))
                       (coe d_zonkF_90 (coe v3) (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.occurs
d_occurs_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 -> Bool
d_occurs_200 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v3 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v5))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v3 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_occurs_200 (coe v0) (coe v3))
                (coe d_occurs_200 (coe v0) (coe v4))
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v3
           -> coe d_occursF_202 (coe v0) (coe v3)
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v3 v4
           -> coe d_occursF_202 (coe v0) (coe v3)
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v3
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
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 -> Bool
d_occursF_202 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v2
        -> coe d_occurs_200 (coe v0) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occursF_202 (coe v0) (coe v2))
             (coe d_occursF_202 (coe v0) (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_occursF_202 (coe v0) (coe v2))
             (coe d_occursF_202 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.bindVar
d_bindVar_274 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bindVar_274 v0 v1 v2 v3
  = coe
      du_go_288 (coe v1) (coe v3)
      (coe d_zonk_88 (coe v0) (coe v3) (coe v2))
-- Once.TypeCheck.Principal._.go
d_go_288 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_288 ~v0 v1 ~v2 v3 v4 = du_go_288 v1 v3 v4
du_go_288 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_288 v0 v1 v2
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
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
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
d_unify_302 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify_302 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_unify''_304 (coe v4) (coe v1)
                (coe d_walk_58 (coe v4) (coe v1) (coe v2))
                (coe d_walk_58 (coe v4) (coe v1) (coe v3)))
-- Once.TypeCheck.Principal.unify'
d_unify''_304 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify''_304 v0 v1 v2 v3
  = let v4
          = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v3 of
                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
                   -> coe d_bindVar_274 (coe v0) (coe v5) (coe v2) (coe v1)
                 _ -> coe v4) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
                  -> coe d_bindVar_274 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
                  -> coe d_bindVar_274 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v7 v8
                  -> coe
                       d_unify2_306 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v7
                  -> coe d_bindVar_274 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v7 v8
                  -> coe
                       d_unify2_306 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v7
                  -> coe d_bindVar_274 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v5 v6 v7
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                          (coe
                             MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'q__8 (coe v6) (coe v9)))
                       (coe
                          d_unify2_306 (coe v0) (coe v1) (coe v5) (coe v8) (coe v7)
                          (coe v10))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v8
                  -> coe d_bindVar_274 (coe v0) (coe v8) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v7 v8
                  -> coe
                       d_unify2_306 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v7
                  -> coe d_bindVar_274 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v7 v8
                  -> coe
                       d_unify2_306 (coe v0) (coe v1) (coe v5) (coe v7) (coe v6) (coe v8)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v7
                  -> coe d_bindVar_274 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v5
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v6
                  -> coe d_unifyF_308 (coe v0) (coe v1) (coe v5) (coe v6)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v6
                  -> coe d_bindVar_274 (coe v0) (coe v6) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v5 v6
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe MAlonzo.Code.Once.Type.d_purityEqBool_188 (coe v6) (coe v8))
                       (coe d_unifyF_308 (coe v0) (coe v1) (coe v5) (coe v7))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v7
                  -> coe d_bindVar_274 (coe v0) (coe v7) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
                  -> coe d_bindVar_274 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
           -> case coe v3 of
                MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
                  -> coe d_bindVar_274 (coe v0) (coe v5) (coe v2) (coe v1)
                _ -> coe v4
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
           -> coe d_bindVar_274 (coe v0) (coe v5) (coe v3) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.unify2
d_unify2_306 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unify2_306 v0 v1 v2 v3 v4 v5
  = let v6 = d_unify_302 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
           -> coe d_unify_302 (coe v0) (coe v7) (coe v4) (coe v5)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.unifyF
d_unifyF_308 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_unifyF_308 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v6
                     -> case coe v3 of
                          MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v7
                            -> coe d_unify_302 (coe v4) (coe v1) (coe v6) (coe v7)
                          _ -> coe v5
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
                     -> case coe v3 of
                          MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
                            -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                          _ -> coe v5
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v6 v7
                     -> case coe v3 of
                          MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v8 v9
                            -> let v10 = d_unifyF_308 (coe v4) (coe v1) (coe v6) (coe v8) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe d_unifyF_308 (coe v4) (coe v11) (coe v7) (coe v9)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v5
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v6 v7
                     -> case coe v3 of
                          MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v8 v9
                            -> let v10 = d_unifyF_308 (coe v4) (coe v1) (coe v6) (coe v8) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe d_unifyF_308 (coe v4) (coe v11) (coe v7) (coe v9)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v5
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Principal.typeToPoly
d_typeToPoly_570 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_typeToPoly_570 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             d_map2P_6 (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24)
             (coe d_typeToPoly_570 (coe v1)) (coe d_typeToPoly_570 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             d_map2P_6 (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26)
             (coe d_typeToPoly_570 (coe v1)) (coe d_typeToPoly_570 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                      -> coe
                           d_map2P_6
                           (coe
                              (\ v6 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 (coe v6)
                                   (coe v4)))
                           (coe d_typeToPoly_570 (coe v1)) (coe d_typeToPoly_570 (coe v3))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                      -> case coe v4 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> coe
                                  d_map2P_6 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32)
                                  (coe d_typeToPoly_570 (coe v1)) (coe d_typeToPoly_570 (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
                      -> let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                         coe
                           (case coe v4 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                -> coe
                                     d_map2P_6 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30)
                                     (coe d_typeToPoly_570 (coe v1)) (coe d_typeToPoly_570 (coe v3))
                              _ -> coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> let v2 = d_functorToPoly_572 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> let v3 = d_functorToPoly_572 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 (coe v4) (coe v2))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.functorToPoly
d_functorToPoly_572 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8
d_functorToPoly_572 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v1
        -> let v2 = d_typeToPoly_570 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.C_Id_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14)
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v1 v2
        -> coe
             d_map2F_14 (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16)
             (coe d_functorToPoly_572 (coe v1))
             (coe d_functorToPoly_572 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v1 v2
        -> coe
             d_map2F_14 (coe MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18)
             (coe d_functorToPoly_572 (coe v1))
             (coe d_functorToPoly_572 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.builtinSchema
d_builtinSchema_666 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinSchema_666 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe v1))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("case" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                 (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1)))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe v1))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe v1))))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe v1))))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1))))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe v1))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                              (coe d_mv_22 (coe addInt (coe (2 :: Integer)) (coe v1))))
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                 (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))))))
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                           (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                        (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe addInt (coe (2 :: Integer)) (coe v1)))
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20))
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20) (coe v1))
         _ -> coe v2)
-- Once.TypeCheck.Principal.lookupRen
d_lookupRen_692 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lookupRen_692 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupRen_692 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.freshen
d_freshen_722 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshen_722 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_722 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_722 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_722 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_722 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))
                   (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_722 (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_722 (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_722 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_722 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen_722 (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen_722 (coe v4) (coe v1) (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen_722 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen_722 (coe v4) (coe v1) (coe v2))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF_724 (coe v4) (coe v1) (coe v2))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF_724 (coe v4) (coe v1) (coe v2)))
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF_724 (coe v4) (coe v1) (coe v2)))
                   (coe v5))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF_724 (coe v4) (coe v1) (coe v2)))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
           -> let v5 = d_lookupRen_692 (coe v4) (coe v2) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe v6))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                   (coe d_mv_22 (coe v1)))
                                (coe v2)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v3)
-- Once.TypeCheck.Principal.freshenF
d_freshenF_724 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshenF_724 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshen_722 (coe v3) (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_freshen_722 (coe v3) (coe v1) (coe v2)))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF_724 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF_724 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_724 (coe v3) (coe v1) (coe v2)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF_724 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF_724 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF_724 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF_724 (coe v3) (coe v1) (coe v2)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF_724 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF_724 (coe v3) (coe v1) (coe v2))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.Env
d_Env_940 :: ()
d_Env_940 = erased
-- Once.TypeCheck.Principal.lookupEnv
d_lookupEnv_942 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_lookupEnv_942 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupEnv_942 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.Result
d_Result_972 :: ()
d_Result_972 = erased
-- Once.TypeCheck.Principal.fuelD
d_fuelD_974 :: Integer
d_fuelD_974 = coe (500 :: Integer)
-- Once.TypeCheck.Principal.retTy
d_retTy_976 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_retTy_976 v0 v1 v2
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
d_SchemaCtx_984 :: ()
d_SchemaCtx_984 = erased
-- Once.TypeCheck.Principal.projSchemas
d_projSchemas_986 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_projSchemas_986 v0
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
                           (coe d_projSchemas_986 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.lookupSchema
d_lookupSchema_994 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_lookupSchema_994 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupSchema_994 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.canonKey
d_canonKey_1024 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_canonKey_1024 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> let v2
                 = MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v0) in
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
                                                   MAlonzo.Code.Once.Spec.Name.d_generatorNS_18)) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> if coe v8
                                               then coe seq (coe v9) (coe v5)
                                               else coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                                                         (coe v0))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.lookupName
d_lookupName_1044 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupName_1044 v0 v1 v2 v3
  = let v4 = d_builtinSchema_666 (coe v2) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5 -> coe v4
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v5 = d_lookupSchema_994 (coe v1) (coe v2) in
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
                                   d_freshen_722 (coe v6) (coe v3)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_freshen_722 (coe v6) (coe v3)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v6
                              = MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupImport_38
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> let v8 = d_typeToPoly_570 (coe v7) in
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
d_liftName_1150 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftName_1150 v0 v1
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
d_arrowParts_1158 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowParts_1158 v0 v1 v2
  = coe
      du_go_1170 (coe v0) (coe v2)
      (coe d_walk_58 (coe d_fuelD_974) (coe v0) (coe v1))
-- Once.TypeCheck.Principal._.go
d_go_1170 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1170 v0 ~v1 v2 v3 = du_go_1170 v0 v2 v3
du_go_1170 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1170 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v4 v5 v6
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
         MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v4 v5
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
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                        (coe
                           MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                           (coe
                              d_occurs_200 (coe v4)
                              (let v5 = d_mv_22 (coe v1) in
                               coe
                                 (let v6 = d_lookupP_28 (coe d_mv_22 (coe v1)) (coe v0) in
                                  coe
                                    (let v7 = 498 :: Integer in
                                     coe
                                       (case coe v6 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                            -> coe d_zonk_88 (coe v7) (coe v0) (coe v8)
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> coe
                                                 MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                                 (coe v5)
                                          _ -> MAlonzo.RTE.mazUnreachableError)))))
                           (coe
                              d_occurs_200 (coe v4)
                              (coe
                                 d_zonk_88 (coe (499 :: Integer)) (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                    (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))))
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                                    (let v5 = d_mv_22 (coe v1) in
                                     coe
                                       (let v6 = d_lookupP_28 (coe d_mv_22 (coe v1)) (coe v0) in
                                        coe
                                          (let v7 = 498 :: Integer in
                                           coe
                                             (case coe v6 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                  -> coe d_zonk_88 (coe v7) (coe v0) (coe v8)
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> coe
                                                       MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                                       (coe v5)
                                                _ -> MAlonzo.RTE.mazUnreachableError))))
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe
                                       d_zonk_88 (coe (499 :: Integer)) (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                          (coe
                                             d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1)))))))
                              (coe v0))) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v1)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                   (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v1))))
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
d_appFinish_1192 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appFinish_1192 v0 v1 v2 v3
  = let v4
          = coe
              du_go_1170 (coe v3) (coe v2)
              (coe d_walk_58 (coe (500 :: Integer)) (coe v3) (coe v0)) in
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
                                                = d_unify''_304
                                                    (coe (499 :: Integer)) (coe v12)
                                                    (coe
                                                       d_walk_58 (coe (499 :: Integer)) (coe v12)
                                                       (coe v6))
                                                    (coe
                                                       d_walk_58 (coe (499 :: Integer)) (coe v12)
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
                                                               MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20)
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
d_composeFinish_1274 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_composeFinish_1274 v0 v1 v2 v3
  = let v4
          = coe
              du_go_1170 (coe v3) (coe v2)
              (coe d_walk_58 (coe (500 :: Integer)) (coe v3) (coe v0)) in
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
                                                    du_go_1170 (coe v12) (coe v13)
                                                    (coe
                                                       d_walk_58 (coe (500 :: Integer)) (coe v12)
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
                                                                                      = d_unify''_304
                                                                                          (coe
                                                                                             (499 ::
                                                                                                Integer))
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             d_walk_58
                                                                                             (coe
                                                                                                (499 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v22)
                                                                                             (coe
                                                                                                v18))
                                                                                          (coe
                                                                                             d_walk_58
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
                                                                                                     MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        v8))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
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
d_pInfer_1426 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInfer_1426 v0 v1 v2 v3 v4 v5
  = let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v7
           -> let v8 = d_lookupEnv_942 (coe v7) (coe v2) in
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
                          d_liftName_1150
                          (coe d_lookupName_1044 (coe v0) (coe v1) (coe v7) (coe v4))
                          (coe v5)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v7
           -> coe
                d_liftName_1150
                (coe
                   d_lookupName_1044 (coe v0) (coe v1) (coe d_canonKey_1024 (coe v7))
                   (coe v4))
                (coe v5)
         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v7 v8
           -> coe
                d_pInferApp_1428 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
                (coe v4) (coe v5)
         MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v7 v8
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                            (coe d_mv_22 (coe v4))))
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
                                        MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                           (coe d_mv_22 (coe v4)))
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10))
                                     (coe v11)))
                        _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v7 v8 v9
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda1_1542 (coe v0) (coe v1) (coe v2) (coe v7)
                   (coe v9))
         MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v7 v8
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda2_1564 (coe v0) (coe v1) (coe v2) (coe v8))
         MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v7 v8 v9 v10 v11
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda4_1600 (coe v0) (coe v1) (coe v2) (coe v8)
                   (coe v9) (coe v10) (coe v11))
         MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))
         MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))
         MAlonzo.Code.Once.Lang.Syntax.C_RStringLit_58 v7
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v7 v8
           -> let v9 = d_typeToPoly_570 (coe v8) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                     -> coe
                          MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                          (coe
                             d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                             (coe v5))
                          (coe
                             (\ v11 ->
                                case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> case coe v13 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                           -> coe
                                                d_retTy_976 (coe v10) (coe v14)
                                                (coe
                                                   d_unify_302 (coe d_fuelD_974) (coe v15) (coe v12)
                                                   (coe v10))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v7 v8 v9
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   du_'46'extendedlambda6_1710 (coe v0) (coe v1) (coe v2) (coe v7)
                   (coe v9))
         MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v8
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4)
                   (coe v5))
                (coe
                   (\ v9 ->
                      case coe v9 of
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                          -> case coe v11 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                 -> coe
                                      d_retTy_976 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)
                                      (coe v12)
                                      (coe
                                         d_unify_302 (coe d_fuelD_974) (coe v13) (coe v10)
                                         (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38))
                               _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> coe v6)
-- Once.TypeCheck.Principal.pInferApp
d_pInferApp_1428 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInferApp_1428 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_pAppGen_1432
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v10
                  -> coe
                       d_pInferAppB_1430 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                       (coe v4) (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                          (coe
                             MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Spec.Name.C_canonical_12
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
d_pInferAppB_1430 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pInferAppB_1430 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe
                d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                (coe v7))
             (coe
                du_'46'extendedlambda10_1798 (coe v0) (coe v1) (coe v2) (coe v5))
      else coe
             d_pAppGen_1432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe v6) (coe v7)
-- Once.TypeCheck.Principal.pAppGen
d_pAppGen_1432 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pAppGen_1432 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
      (coe
         d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
         (coe v6))
      (coe
         du_'46'extendedlambda12_1844 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.TypeCheck.Principal.destructFinish
d_destructFinish_1434 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_destructFinish_1434 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = d_unify''_304
              (coe (499 :: Integer)) (coe v9)
              (coe d_walk_58 (coe (499 :: Integer)) (coe v9) (coe v7))
              (coe
                 d_walk_58 (coe (499 :: Integer)) (coe v9)
                 (coe
                    MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe d_mv_22 (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                       (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v8)))))) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
           -> coe
                MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                (coe
                   d_pInfer_1426 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                         (coe
                            MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                            (coe d_mv_22 (coe v8))))
                      (coe v2))
                   (coe v4) (coe addInt (coe (2 :: Integer)) (coe v8)) (coe v11))
                (coe
                   du_'46'extendedlambda14_1926 (coe v8) (coe v0) (coe v1) (coe v2)
                   (coe v5) (coe v6))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal..extendedlambda1
d_'46'extendedlambda1_1542 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda1_1542 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda1_1542 v0 v1 v2 v3 v5 v8
du_'46'extendedlambda1_1542 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda1_1542 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    d_pInfer_1426 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6))
                       (coe v2))
                    (coe v4) (coe v8) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda2
d_'46'extendedlambda2_1564 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda2_1564 v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_'46'extendedlambda2_1564 v0 v1 v2 v4 v7
du_'46'extendedlambda2_1564 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda2_1564 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
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
                                            MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 (coe v5)
                                            (coe v10))
                                         (coe v11)))
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda4
d_'46'extendedlambda4_1600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda4_1600 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10
  = du_'46'extendedlambda4_1600 v0 v1 v2 v4 v5 v6 v7 v10
du_'46'extendedlambda4_1600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda4_1600 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    d_destructFinish_1434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v8) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda6
d_'46'extendedlambda6_1710 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda6_1710 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda6_1710 v0 v1 v2 v3 v5 v8
du_'46'extendedlambda6_1710 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda6_1710 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_retTy_976 (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)
                       (coe v8)
                       (coe
                          d_unify_302 (coe d_fuelD_974) (coe v9) (coe v6)
                          (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38)))
                    (coe
                       du_'46'extendedlambda7_1718 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda7
d_'46'extendedlambda7_1718 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda7_1718 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10
                           v11
  = du_'46'extendedlambda7_1718 v0 v1 v2 v3 v5 v9 v11
du_'46'extendedlambda7_1718 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda7_1718 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                       (coe v10))
                    (coe
                       (\ v11 ->
                          case coe v11 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                              -> case coe v13 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                     -> coe
                                          d_retTy_976
                                          (coe
                                             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                             (coe
                                                MAlonzo.Code.Once.Lang.Syntax.d_isComparisonOp_68
                                                (coe v3))
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                                                (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20)
                                                (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20))
                                             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38))
                                          (coe v14)
                                          (coe
                                             d_unify_302 (coe d_fuelD_974) (coe v15) (coe v12)
                                             (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda10
d_'46'extendedlambda10_1798 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda10_1798 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_'46'extendedlambda10_1798 v0 v1 v2 v5 v8
du_'46'extendedlambda10_1798 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda10_1798 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
                    (coe
                       (\ v9 ->
                          case coe v9 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                              -> case coe v11 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                     -> coe
                                          d_composeFinish_1274 (coe v5) (coe v10) (coe v12)
                                          (coe v13)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda12
d_'46'extendedlambda12_1844 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda12_1844 v0 v1 v2 ~v3 v4 ~v5 ~v6 v7
  = du_'46'extendedlambda12_1844 v0 v1 v2 v4 v7
du_'46'extendedlambda12_1844 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda12_1844 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_pInfer_1426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
                    (coe
                       (\ v9 ->
                          case coe v9 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                              -> case coe v11 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                     -> coe d_appFinish_1192 (coe v5) (coe v10) (coe v12) (coe v13)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal..extendedlambda14
d_'46'extendedlambda14_1926 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda14_1926 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 v10
                            v11
  = du_'46'extendedlambda14_1926 v1 v4 v5 v6 v9 v10 v11
du_'46'extendedlambda14_1926 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'46'extendedlambda14_1926 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       d_pInfer_1426 (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                                (coe d_mv_22 (coe addInt (coe (1 :: Integer)) (coe v0)))))
                          (coe v3))
                       (coe v5) (coe v9) (coe v10))
                    (coe
                       (\ v11 ->
                          case coe v11 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                              -> case coe v13 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                     -> coe
                                          d_retTy_976 (coe v7) (coe v14)
                                          (coe
                                             d_unify_302 (coe d_fuelD_974) (coe v15) (coe v7)
                                             (coe v12))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.renameVars
d_renameVars_1942 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_renameVars_1942 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         d_freshen''_1954 (coe v0) (coe v0) (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.TypeCheck.Principal._.letter
d_letter_1950 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_letter_1950 ~v0 v1 = du_letter_1950 v1
du_letter_1950 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_letter_1950 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("t" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Principal._.freshen'
d_freshen''_1954 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshen''_1954 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1954 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1954 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1954 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1954 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v5 v6 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1954 (coe v0) (coe v7)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1954 (coe v0) (coe v7)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1954 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1954 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_freshen''_1954 (coe v0) (coe v6)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      d_freshen''_1954 (coe v0) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshen''_1954 (coe v0) (coe v5) (coe v2) (coe v3))))))
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF''_1956 (coe v0) (coe v5) (coe v2) (coe v3))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF''_1956 (coe v0) (coe v5) (coe v2) (coe v3)))
         MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe d_freshenF''_1956 (coe v0) (coe v5) (coe v2) (coe v3)))
                   (coe v6))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe d_freshenF''_1956 (coe v0) (coe v5) (coe v2) (coe v3)))
         MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v5
           -> let v6 = d_lookupRen_692 (coe v5) (coe v3) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42
                             (coe du_letter_1950 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v2))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                   (coe du_letter_1950 (coe v2)))
                                (coe v3)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v4)
-- Once.TypeCheck.Principal._.freshenF'
d_freshenF''_1956 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_freshenF''_1956 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshen''_1954 (coe v0) (coe v4) (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_freshen''_1954 (coe v0) (coe v4) (coe v2) (coe v3)))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF''_1956 (coe v0) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF''_1956 (coe v0) (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      d_freshenF''_1956 (coe v0) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3)))))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_freshenF''_1956 (coe v0) (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe d_freshenF''_1956 (coe v0) (coe v4) (coe v2) (coe v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.groundOr
d_groundOr_2172 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_groundOr_2172 v0
  = let v1 = MAlonzo.Code.Once.Type.d_isGround_104 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Poly.d_extractGround_88 (coe v0)
                      (coe v2)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                   (coe d_renameVars_1942 (coe v0)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Principal.finishP
d_finishP_2186 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_finishP_2186 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           d_groundOr_2172 (coe d_zonk_88 (coe d_fuelD_974) (coe v5) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Principal.principal
d_principal_2192 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_principal_2192 v0 v1
  = coe
      d_finishP_2186
      (coe
         d_pInfer_1426
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v0))
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0)))
         (coe
            d_projSchemas_986
            (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.TypeCheck.Principal.pgProj
d_pgProj_2198 ::
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8
d_pgProj_2198 v0
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
d_principalGround_2202 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8
d_principalGround_2202 v0 v1
  = coe d_pgProj_2198 (coe d_principal_2192 (coe v0) (coe v1))
-- Once.TypeCheck.Principal.pgSchema
d_pgSchema_2208 ::
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_pgSchema_2208 v0
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
d_siglessSchema_2212 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_siglessSchema_2212 v0
  = coe
      d_pgSchema_2208
      (coe
         d_principal_2192
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_330) (coe v0))
