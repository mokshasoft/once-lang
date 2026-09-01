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

module MAlonzo.Code.Once.TypeCheck.DeciderComplete where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.TypeCheck.DeciderComplete.wellFormedF?-complete
d_wellFormedF'63''45'complete_10 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wellFormedF'63''45'complete_10 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v3
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> let v5
                        = MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                            (coe v4) (coe v3) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v6) erased
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__114 v6 v7
               -> let v8 = d_wellFormedF'63''45'complete_10 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_wellFormedF'63''45'complete_10 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v10
                                           v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__116 v6 v7
               -> let v8 = d_wellFormedF'63''45'complete_10 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_wellFormedF'63''45'complete_10 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v10
                                           v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.DeciderComplete.wellFormedF?-complete-at
d_wellFormedF'63''45'complete'45'at_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wellFormedF'63''45'complete'45'at_88 = erased
-- Once.TypeCheck.DeciderComplete.isGroundF-complete
d_isGroundF'45'complete_110 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isGroundF'45'complete_110 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PK_242 v2
        -> coe d_isGround'45'complete_116 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_PId_244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C__P'8853'__246 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d_isGroundF'45'complete_110 (coe v2) (coe v4) in
                  coe
                    (let v7 = d_isGroundF'45'complete_110 (coe v3) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v10))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8855'__248 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d_isGroundF'45'complete_110 (coe v2) (coe v4) in
                  coe
                    (let v7 = d_isGroundF'45'complete_110 (coe v3) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v10))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.DeciderComplete.isGround-complete
d_isGround'45'complete_116 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isGround'45'complete_116 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_PUnit_250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C_PVoid_252
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C__P'42'__254 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d_isGround'45'complete_116 (coe v2) (coe v4) in
                  coe
                    (let v7 = d_isGround'45'complete_116 (coe v3) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v10))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'43'__256 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d_isGround'45'complete_116 (coe v2) (coe v4) in
                  coe
                    (let v7 = d_isGround'45'complete_116 (coe v3) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v10))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> let v7 = d_isGround'45'complete_116 (coe v2) (coe v5) in
                  coe
                    (let v8 = d_isGround'45'complete_116 (coe v4) (coe v6) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                           (coe v11))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_PEff_260 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6 = d_isGround'45'complete_116 (coe v2) (coe v4) in
                  coe
                    (let v7 = d_isGround'45'complete_116 (coe v3) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v10))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Pμ'45'type_262 v2
        -> coe d_isGroundF'45'complete_110 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Pν'45'type_264 v2
        -> coe d_isGroundF'45'complete_110 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_PInt_266
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C_PFloat_268
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C_PStr_270
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      MAlonzo.Code.Once.Type.C_PBuffer_272
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.DeciderComplete.isGround-inj₂-¬Ground
d_isGround'45'inj'8322''45''172'Ground_352 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''45''172'Ground_352 = erased
-- Once.TypeCheck.DeciderComplete.¬Ground-isGround-inj₂
d_'172'Ground'45'isGround'45'inj'8322'_394 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'Ground'45'isGround'45'inj'8322'_394 = erased
-- Once.TypeCheck.DeciderComplete.GroundF-irrelevant
d_GroundF'45'irrelevant_420 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_GroundF'45'irrelevant_420 = erased
-- Once.TypeCheck.DeciderComplete.Ground-irrelevant
d_Ground'45'irrelevant_428 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Ground'45'irrelevant_428 = erased
-- Once.TypeCheck.DeciderComplete.isGround-complete-at
d_isGround'45'complete'45'at_526 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isGround'45'complete'45'at_526 = erased
