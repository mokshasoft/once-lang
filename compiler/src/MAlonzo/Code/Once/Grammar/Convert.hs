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

module MAlonzo.Code.Once.Grammar.Convert where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.Convert.gtypeToType
d_gtypeToType_6 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_gtypeToType_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Unit_120)
      MAlonzo.Code.Once.Grammar.C_TVoid_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Void_122)
      MAlonzo.Code.Once.Grammar.C_TInt_16
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Int_134)
      MAlonzo.Code.Once.Grammar.C_TFloat_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Float_136)
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__20 v1 v2 v3
        -> let v4 = d_gtypeToType_6 (coe v1) in
           coe
             (let v5 = d_gtypeToType_6 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v2)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8855'__22 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C__'8853'__24 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_TEff_26 v1 v2
        -> let v3 = d_gtypeToType_6 (coe v1) in
           coe
             (let v4 = d_gtypeToType_6 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_GMu_28 v1
        -> let v2 = d_gfunctorToFunctor_8 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_GNu_30 v1
        -> let v2 = d_gfunctorToFunctor_8 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v3)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_GNuEff_32 v1
        -> let v2 = d_gfunctorToFunctor_8 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v3)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_TVar_34 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.gfunctorToFunctor
d_gfunctorToFunctor_8 ::
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  Maybe MAlonzo.Code.Once.Type.T_Functor_106
d_gfunctorToFunctor_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_GFK_36 v1
        -> let v2 = d_gtypeToType_6 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_K_112 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_GFId_38
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Type.C_Id_114)
      MAlonzo.Code.Once.Grammar.C_GFSum_40 v1 v2
        -> let v3 = d_gfunctorToFunctor_8 (coe v1) in
           coe
             (let v4 = d_gfunctorToFunctor_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'8853'__116 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_GFProd_42 v1 v2
        -> let v3 = d_gfunctorToFunctor_8 (coe v1) in
           coe
             (let v4 = d_gfunctorToFunctor_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Type.C__'8855'__118 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.typeToGType
d_typeToGType_184 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Grammar.T_GType_8
d_typeToGType_184 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TUnit_12)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TVoid_14)
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> let v3 = d_typeToGType_184 (coe v1) in
           coe
             (let v4 = d_typeToGType_184 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C__'8855'__22 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> let v3 = d_typeToGType_184 (coe v1) in
           coe
             (let v4 = d_typeToGType_184 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C__'8853'__24 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_pure_34
                      -> let v6 = d_typeToGType_184 (coe v1) in
                         coe
                           (let v7 = d_typeToGType_184 (coe v3) in
                            coe
                              (case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__20
                                                  (coe v8) (coe v4) (coe v9))
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    MAlonzo.Code.Once.Type.C_eff_36
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v6 = d_typeToGType_184 (coe v1) in
                                coe
                                  (let v7 = d_typeToGType_184 (coe v3) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Once.Grammar.C_TEff_26
                                                         (coe v8) (coe v9))
                                               _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> let v2 = d_functorToGFunctor_186 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Grammar.C_GMu_28 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> let v3 = d_functorToGFunctor_186 (coe v1) in
                  coe
                    (case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Once.Grammar.C_GNu_30 (coe v4))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C_eff_36
               -> let v3 = d_functorToGFunctor_186 (coe v1) in
                  coe
                    (case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Once.Grammar.C_GNuEff_32 (coe v4))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TInt_16)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_TFloat_18)
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.functorToGFunctor
d_functorToGFunctor_186 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Grammar.T_GFunctor_10
d_functorToGFunctor_186 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> let v2 = d_typeToGType_184 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Grammar.C_GFK_36 (coe v3))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Grammar.C_GFId_38)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> let v3 = d_functorToGFunctor_186 (coe v1) in
           coe
             (let v4 = d_functorToGFunctor_186 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C_GFSum_40 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> let v3 = d_functorToGFunctor_186 (coe v1) in
           coe
             (let v4 = d_functorToGFunctor_186 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Grammar.C_GFProd_42 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.typeToGType-gtypeToType
d_typeToGType'45'gtypeToType_366 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typeToGType'45'gtypeToType_366 = erased
-- Once.Grammar.Convert.functorToGFunctor-gfunctorToFunctor
d_functorToGFunctor'45'gfunctorToFunctor_372 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_functorToGFunctor'45'gfunctorToFunctor_372 = erased
-- Once.Grammar.Convert.gtypeToType-typeToGType
d_gtypeToType'45'typeToGType_654 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gtypeToType'45'typeToGType_654 = erased
-- Once.Grammar.Convert.gfunctorToFunctor-functorToGFunctor
d_gfunctorToFunctor'45'functorToGFunctor_660 ::
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gfunctorToFunctor'45'functorToGFunctor_660 = erased
-- Once.Grammar.Convert.GrammarExpressible
d_GrammarExpressible_938 :: MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_GrammarExpressible_938 = erased
-- Once.Grammar.Convert.parseGType
d_parseGType_944 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseGType_944 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Type.du_stripType_2804
              (let v1
                     = coe
                         MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_130 (coe v0) in
               coe
                 (case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_152
                                                 (coe v3) (coe v5) in
                                       coe
                                         (case coe v7 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                            -> let v13
                                                                     = coe
                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_200
                                                                         v5 v3 v6 v12 in
                                                               coe
                                                                 (let v14
                                                                        = coe
                                                                            MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
                                                                            (coe v9) (coe v11) in
                                                                  coe
                                                                    (case coe v14 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                         -> case coe v15 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                -> case coe v17 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                       -> let v20
                                                                                                = coe
                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                                    v11
                                                                                                    v9
                                                                                                    v13
                                                                                                    v19 in
                                                                                          coe
                                                                                            (let v21
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                                       (coe
                                                                                                          v16)
                                                                                                       (coe
                                                                                                          v18) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v21 of
                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                                    -> case coe
                                                                                                              v22 of
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                           -> case coe
                                                                                                                     v24 of
                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                  -> coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                          (coe
                                                                                                                             v23)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                             (coe
                                                                                                                                v25)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                                v18
                                                                                                                                v16
                                                                                                                                v20
                                                                                                                                v26)))
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                    -> coe
                                                                                                         v21
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                       -> case coe
                                                                                                 v17 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                              -> let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              v18) in
                                                                                                 coe
                                                                                                   (case coe
                                                                                                           v20 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                        -> case coe
                                                                                                                  v21 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                               -> case coe
                                                                                                                         v23 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                      -> coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v22)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                 (coe
                                                                                                                                    v24)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                                    v18
                                                                                                                                    v16
                                                                                                                                    v19
                                                                                                                                    v25)))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                        -> coe
                                                                                                             v20
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                -> coe v14
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                              -> case coe v7 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                   -> let v13
                                                                            = coe
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
                                                                                (coe v9)
                                                                                (coe v11) in
                                                                      coe
                                                                        (case coe v13 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                             -> case coe v14 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                    -> case coe
                                                                                              v16 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                           -> let v19
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                                        v11
                                                                                                        v9
                                                                                                        v12
                                                                                                        v18 in
                                                                                              coe
                                                                                                (let v20
                                                                                                       = coe
                                                                                                           MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                                           (coe
                                                                                                              v15)
                                                                                                           (coe
                                                                                                              v17) in
                                                                                                 coe
                                                                                                   (case coe
                                                                                                           v20 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                        -> case coe
                                                                                                                  v21 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                               -> case coe
                                                                                                                         v23 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                      -> coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v22)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                 (coe
                                                                                                                                    v24)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                                    v17
                                                                                                                                    v15
                                                                                                                                    v19
                                                                                                                                    v25)))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                        -> coe
                                                                                                             v20
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> let v19
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                                               (coe
                                                                                                                  v15)
                                                                                                               (coe
                                                                                                                  v17) in
                                                                                                     coe
                                                                                                       (case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                            -> case coe
                                                                                                                      v20 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                   -> case coe
                                                                                                                             v22 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                                          -> coe
                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                  (coe
                                                                                                                                     v21)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                     (coe
                                                                                                                                        v23)
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                                        v17
                                                                                                                                        v15
                                                                                                                                        v18
                                                                                                                                        v24)))
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                            -> coe
                                                                                                                 v19
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> coe v13
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                            -> case coe v8 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                                   -> case coe v10 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                          -> let v13
                                                                                   = coe
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                       (coe v9)
                                                                                       (coe v11) in
                                                                             coe
                                                                               (case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v15)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                v17)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                v11
                                                                                                                v9
                                                                                                                v12
                                                                                                                v18)))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> coe v13
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> coe v7
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> case coe v1 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                             -> case coe v2 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                                    -> case coe v4 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                           -> let v7
                                                    = coe
                                                        MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_158
                                                        (coe v3) (coe v5) in
                                              coe
                                                (case coe v7 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                   -> let v13
                                                                            = coe
                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_232
                                                                                v5 v3 v6 v12 in
                                                                      coe
                                                                        (let v14
                                                                               = coe
                                                                                   MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                   (coe v9)
                                                                                   (coe v11) in
                                                                         coe
                                                                           (case coe v14 of
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                       -> case coe
                                                                                                 v17 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         v16)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            v18)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                            v11
                                                                                                            v9
                                                                                                            v13
                                                                                                            v19)))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                -> coe v14
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                            -> case coe v8 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                                   -> case coe v10 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                          -> let v13
                                                                                   = coe
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                                                       (coe v9)
                                                                                       (coe v11) in
                                                                             coe
                                                                               (case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v15)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                v17)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                                                v11
                                                                                                                v9
                                                                                                                v12
                                                                                                                v18)))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> coe v13
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> coe v7
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v1 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                                    -> case coe v2 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                                           -> case coe v4 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                                  -> let v7
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_164
                                                               (coe v3) (coe v5) in
                                                     coe
                                                       (case coe v7 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                            -> case coe v8 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                                   -> case coe v10 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v9)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v11)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_264
                                                                                        v5 v3 v6
                                                                                        v12)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> coe v7
                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5 = d_typeToGType_184 (coe v3) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v4))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Grammar.Convert.Expressible
d_Expressible_994 a0 = ()
data T_Expressible_994
  = C_ex'45'unit_998 | C_ex'45'void_1000 | C_ex'45'int_1002 |
    C_ex'45'float_1004 |
    C_ex'45'prod_1010 T_Expressible_994 T_Expressible_994 |
    C_ex'45'sum_1016 T_Expressible_994 T_Expressible_994 |
    C_ex'45'fun_1024 T_Expressible_994 T_Expressible_994 |
    C_ex'45'eff_1030 T_Expressible_994 T_Expressible_994 |
    C_ex'45'mu_1034 T_ExpressibleF_996 |
    C_ex'45'nu_1038 T_ExpressibleF_996 |
    C_ex'45'nu'45'eff_1042 T_ExpressibleF_996
-- Once.Grammar.Convert.ExpressibleF
d_ExpressibleF_996 a0 = ()
data T_ExpressibleF_996
  = C_exf'45'k_1046 T_Expressible_994 | C_exf'45'id_1048 |
    C_exf'45'sum_1054 T_ExpressibleF_996 T_ExpressibleF_996 |
    C_exf'45'prod_1060 T_ExpressibleF_996 T_ExpressibleF_996
-- Once.Grammar.Convert.typeToGType-Expressible
d_typeToGType'45'Expressible_1066 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_Expressible_994 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeToGType'45'Expressible_1066 v0 v1
  = case coe v1 of
      C_ex'45'unit_998
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TUnit_12) erased
      C_ex'45'void_1000
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TVoid_14) erased
      C_ex'45'int_1002
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TInt_16) erased
      C_ex'45'float_1004
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_TFloat_18) erased
      C_ex'45'prod_1010 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> let v8 = d_typeToGType'45'Expressible_1066 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_typeToGType'45'Expressible_1066 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C__'8855'__22 (coe v10)
                                           (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'sum_1016 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> let v8 = d_typeToGType'45'Expressible_1066 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_typeToGType'45'Expressible_1066 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C__'8853'__24 (coe v10)
                                           (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'fun_1024 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                      -> let v12 = d_typeToGType'45'Expressible_1066 (coe v7) (coe v5) in
                         coe
                           (let v13 = d_typeToGType'45'Expressible_1066 (coe v9) (coe v6) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> case coe v13 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__20
                                                  (coe v14) (coe v10) (coe v16))
                                               erased
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'eff_1030 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> let v9 = d_typeToGType'45'Expressible_1066 (coe v6) (coe v4) in
                  coe
                    (let v10 = d_typeToGType'45'Expressible_1066 (coe v8) (coe v5) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C_TEff_26 (coe v11) (coe v13))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'mu_1034 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v4
               -> let v5
                        = d_functorToGFunctor'45'ExpressibleF_1072 (coe v4) (coe v3) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Grammar.C_GMu_28 (coe v6)) erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'nu_1038 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v4 v5
               -> let v6
                        = d_functorToGFunctor'45'ExpressibleF_1072 (coe v4) (coe v3) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Grammar.C_GNu_30 (coe v7)) erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ex'45'nu'45'eff_1042 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v4 v5
               -> let v6
                        = d_functorToGFunctor'45'ExpressibleF_1072 (coe v4) (coe v3) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Grammar.C_GNuEff_32 (coe v7)) erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.Convert.functorToGFunctor-ExpressibleF
d_functorToGFunctor'45'ExpressibleF_1072 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  T_ExpressibleF_996 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_functorToGFunctor'45'ExpressibleF_1072 v0 v1
  = case coe v1 of
      C_exf'45'k_1046 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v4
               -> let v5 = d_typeToGType'45'Expressible_1066 (coe v4) (coe v3) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Grammar.C_GFK_36 (coe v6)) erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_exf'45'id_1048
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Grammar.C_GFId_38) erased
      C_exf'45'sum_1054 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v6 v7
               -> let v8
                        = d_functorToGFunctor'45'ExpressibleF_1072 (coe v6) (coe v4) in
                  coe
                    (let v9
                           = d_functorToGFunctor'45'ExpressibleF_1072 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C_GFSum_40 (coe v10) (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_exf'45'prod_1060 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v6 v7
               -> let v8
                        = d_functorToGFunctor'45'ExpressibleF_1072 (coe v6) (coe v4) in
                  coe
                    (let v9
                           = d_functorToGFunctor'45'ExpressibleF_1072 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Grammar.C_GFProd_42 (coe v10)
                                           (coe v12))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
