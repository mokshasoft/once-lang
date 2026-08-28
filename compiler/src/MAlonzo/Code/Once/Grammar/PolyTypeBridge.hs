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

module MAlonzo.Code.Once.Grammar.PolyTypeBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.PolyInst
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Generic.Sound
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.PolyTypeBridge.ppB-go-sound
d_ppB'45'go'45'sound_18 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
d_ppB'45'go'45'sound_18 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ppB'45'go'45'sound_18 v0 v1
du_ppB'45'go'45'sound_18 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
du_ppB'45'go'45'sound_18 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_370
                (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
                (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.PolyTypeBridge.parsePolyTypeB-sound
d_parsePolyTypeB'45'sound_42 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
d_parsePolyTypeB'45'sound_42 v0 ~v1 ~v2 ~v3 ~v4
  = du_parsePolyTypeB'45'sound_42 v0
du_parsePolyTypeB'45'sound_42 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
du_parsePolyTypeB'45'sound_42 v0
  = coe
      du_ppB'45'go'45'sound_18 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_82
         (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
         (coe v0))
-- Once.Grammar.PolyTypeBridge.ppB-go-complete
d_ppB'45'go'45'complete_60 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ppB'45'go'45'complete_60 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_ppB'45'go'45'complete_60 v0 v1
du_ppB'45'go'45'complete_60 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ppB'45'go'45'complete_60 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_708
                       (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
                       (coe v0) (coe v4)
                       (let v5
                              = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                        coe
                          (let v6
                                 = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                           coe
                             (let v7
                                    = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                              coe
                                (let v8
                                       = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118 in
                                 coe
                                   (let v9
                                          = MAlonzo.Code.Once.Parser.Generic.PolyInst.d_tvarP_46
                                              (coe v0) in
                                    coe
                                      (case coe v9 of
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                           -> case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                         -> let v15
                                                                  = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                      (coe v7) (coe v11)
                                                                      (coe v13) in
                                                            coe
                                                              (case coe v15 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                   -> case coe v16 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                          -> let v19
                                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                       (coe v6)
                                                                                       (coe v17)
                                                                                       (coe v18) in
                                                                             coe
                                                                               (case coe v19 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                    -> case coe
                                                                                              v20 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                           -> let v23
                                                                                                    = let v23
                                                                                                            = coe
                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                                                v5
                                                                                                                v0 in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v23 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                             -> case coe
                                                                                                                       v24 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                    -> case coe
                                                                                                                              v26 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                           -> let v29
                                                                                                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                        (coe
                                                                                                                                           v5)
                                                                                                                                        (coe
                                                                                                                                           v25)
                                                                                                                                        (coe
                                                                                                                                           v27) in
                                                                                                                              coe
                                                                                                                                (case coe
                                                                                                                                        v29 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                     -> case coe
                                                                                                                                               v30 of
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                            -> let v33
                                                                                                                                                     = let v33
                                                                                                                                                             = coe
                                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                                 v28 in
                                                                                                                                                       coe
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                            v27
                                                                                                                                                            v25
                                                                                                                                                            v33
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                               (coe
                                                                                                                                                                  v5)
                                                                                                                                                               (coe
                                                                                                                                                                  v27))) in
                                                                                                                                               coe
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                    v32
                                                                                                                                                    v31
                                                                                                                                                    v33
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                       (coe
                                                                                                                                                          v5)
                                                                                                                                                       (coe
                                                                                                                                                          v32)))
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                             -> let v24
                                                                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                          (coe
                                                                                                                             v5)
                                                                                                                          (coe
                                                                                                                             v0) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v24 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                       -> case coe
                                                                                                                                 v25 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                              -> let v28
                                                                                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                           (coe
                                                                                                                                              v5)
                                                                                                                                           (coe
                                                                                                                                              v26)
                                                                                                                                           (coe
                                                                                                                                              v27) in
                                                                                                                                 coe
                                                                                                                                   (case coe
                                                                                                                                           v28 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                        -> case coe
                                                                                                                                                  v29 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                               -> let v32
                                                                                                                                                        = let v32
                                                                                                                                                                = coe
                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                                    (coe
                                                                                                                                                                       v5)
                                                                                                                                                                    (coe
                                                                                                                                                                       v0) in
                                                                                                                                                          coe
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                               v27
                                                                                                                                                               v26
                                                                                                                                                               v32
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                                  (coe
                                                                                                                                                                     v5)
                                                                                                                                                                  (coe
                                                                                                                                                                     v27))) in
                                                                                                                                                  coe
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                       v31
                                                                                                                                                       v30
                                                                                                                                                       v32
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                          (coe
                                                                                                                                                             v5)
                                                                                                                                                          (coe
                                                                                                                                                             v31)))
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> case coe
                                                                                                                                 v24 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                              -> case coe
                                                                                                                                        v25 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                     -> coe
                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                          v27
                                                                                                                                          v26
                                                                                                                                          erased
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                             (coe
                                                                                                                                                v5)
                                                                                                                                             (coe
                                                                                                                                                v27))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                                              coe
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                                   v22
                                                                                                   v21
                                                                                                   v23
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                                      (coe
                                                                                                         v5)
                                                                                                      (coe
                                                                                                         v22)))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> case coe v15 of
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                          -> case coe v16 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                 -> let v19
                                                                                          = let v19
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                                      v5
                                                                                                      v0 in
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
                                                                                                                 -> let v25
                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                              (coe
                                                                                                                                 v5)
                                                                                                                              (coe
                                                                                                                                 v21)
                                                                                                                              (coe
                                                                                                                                 v23) in
                                                                                                                    coe
                                                                                                                      (case coe
                                                                                                                              v25 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                           -> case coe
                                                                                                                                     v26 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                  -> let v29
                                                                                                                                           = let v29
                                                                                                                                                   = coe
                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                       v24 in
                                                                                                                                             coe
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                  v23
                                                                                                                                                  v21
                                                                                                                                                  v29
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                     (coe
                                                                                                                                                        v5)
                                                                                                                                                     (coe
                                                                                                                                                        v23))) in
                                                                                                                                     coe
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                          v28
                                                                                                                                          v27
                                                                                                                                          v29
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                             (coe
                                                                                                                                                v5)
                                                                                                                                             (coe
                                                                                                                                                v28)))
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                   -> let v20
                                                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                (coe
                                                                                                                   v5)
                                                                                                                (coe
                                                                                                                   v0) in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v20 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                             -> case coe
                                                                                                                       v21 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                    -> let v24
                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                 (coe
                                                                                                                                    v5)
                                                                                                                                 (coe
                                                                                                                                    v22)
                                                                                                                                 (coe
                                                                                                                                    v23) in
                                                                                                                       coe
                                                                                                                         (case coe
                                                                                                                                 v24 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                              -> case coe
                                                                                                                                        v25 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                     -> let v28
                                                                                                                                              = let v28
                                                                                                                                                      = coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                          (coe
                                                                                                                                                             v5)
                                                                                                                                                          (coe
                                                                                                                                                             v0) in
                                                                                                                                                coe
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                     v23
                                                                                                                                                     v22
                                                                                                                                                     v28
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                        (coe
                                                                                                                                                           v5)
                                                                                                                                                        (coe
                                                                                                                                                           v23))) in
                                                                                                                                        coe
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                             v27
                                                                                                                                             v26
                                                                                                                                             v28
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                (coe
                                                                                                                                                   v5)
                                                                                                                                                (coe
                                                                                                                                                   v27)))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                             -> case coe
                                                                                                                       v20 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                                                    -> case coe
                                                                                                                              v21 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                           -> coe
                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                v23
                                                                                                                                v22
                                                                                                                                erased
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                   (coe
                                                                                                                                      v5)
                                                                                                                                   (coe
                                                                                                                                      v23))
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                                    coe
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                         v18 v17 v19
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                            (coe v5)
                                                                                            (coe
                                                                                               v18)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           -> let v10
                                                    = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                        (coe v8) (coe v0) in
                                              coe
                                                (case coe v10 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                            -> let v14
                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                         (coe v7) (coe v12)
                                                                         (coe v13) in
                                                               coe
                                                                 (case coe v14 of
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                      -> case coe v15 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                             -> let v18
                                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                          (coe v6)
                                                                                          (coe v16)
                                                                                          (coe
                                                                                             v17) in
                                                                                coe
                                                                                  (case coe v18 of
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                       -> case coe
                                                                                                 v19 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                              -> let v22
                                                                                                       = let v22
                                                                                                               = coe
                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                                                   v5
                                                                                                                   v0 in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v22 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                                -> case coe
                                                                                                                          v23 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                       -> case coe
                                                                                                                                 v25 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                              -> let v28
                                                                                                                                       = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                           (coe
                                                                                                                                              v5)
                                                                                                                                           (coe
                                                                                                                                              v24)
                                                                                                                                           (coe
                                                                                                                                              v26) in
                                                                                                                                 coe
                                                                                                                                   (case coe
                                                                                                                                           v28 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                        -> case coe
                                                                                                                                                  v29 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                               -> let v32
                                                                                                                                                        = let v32
                                                                                                                                                                = coe
                                                                                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                                    v27 in
                                                                                                                                                          coe
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                               v26
                                                                                                                                                               v24
                                                                                                                                                               v32
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                                  (coe
                                                                                                                                                                     v5)
                                                                                                                                                                  (coe
                                                                                                                                                                     v26))) in
                                                                                                                                                  coe
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                       v31
                                                                                                                                                       v30
                                                                                                                                                       v32
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                          (coe
                                                                                                                                                             v5)
                                                                                                                                                          (coe
                                                                                                                                                             v31)))
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> let v23
                                                                                                                         = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                             (coe
                                                                                                                                v5)
                                                                                                                             (coe
                                                                                                                                v0) in
                                                                                                                   coe
                                                                                                                     (case coe
                                                                                                                             v23 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                          -> case coe
                                                                                                                                    v24 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                 -> let v27
                                                                                                                                          = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                              (coe
                                                                                                                                                 v5)
                                                                                                                                              (coe
                                                                                                                                                 v25)
                                                                                                                                              (coe
                                                                                                                                                 v26) in
                                                                                                                                    coe
                                                                                                                                      (case coe
                                                                                                                                              v27 of
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                                                                           -> case coe
                                                                                                                                                     v28 of
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                  -> let v31
                                                                                                                                                           = let v31
                                                                                                                                                                   = coe
                                                                                                                                                                       MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                                       (coe
                                                                                                                                                                          v5)
                                                                                                                                                                       (coe
                                                                                                                                                                          v0) in
                                                                                                                                                             coe
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                                  v26
                                                                                                                                                                  v25
                                                                                                                                                                  v31
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                                     (coe
                                                                                                                                                                        v5)
                                                                                                                                                                     (coe
                                                                                                                                                                        v26))) in
                                                                                                                                                     coe
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                          v30
                                                                                                                                                          v29
                                                                                                                                                          v31
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                             (coe
                                                                                                                                                                v5)
                                                                                                                                                             (coe
                                                                                                                                                                v30)))
                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> case coe
                                                                                                                                    v23 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                                 -> case coe
                                                                                                                                           v24 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                        -> coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                             v26
                                                                                                                                             v25
                                                                                                                                             erased
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                (coe
                                                                                                                                                   v5)
                                                                                                                                                (coe
                                                                                                                                                   v26))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                                                 coe
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                                      v21
                                                                                                      v20
                                                                                                      v22
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                                         (coe
                                                                                                            v5)
                                                                                                         (coe
                                                                                                            v21)))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      -> case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                             -> case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                    -> let v18
                                                                                             = let v18
                                                                                                     = coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                                         v5
                                                                                                         v0 in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v18 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                      -> case coe
                                                                                                                v19 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                             -> case coe
                                                                                                                       v21 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                    -> let v24
                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                 (coe
                                                                                                                                    v5)
                                                                                                                                 (coe
                                                                                                                                    v20)
                                                                                                                                 (coe
                                                                                                                                    v22) in
                                                                                                                       coe
                                                                                                                         (case coe
                                                                                                                                 v24 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                              -> case coe
                                                                                                                                        v25 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                     -> let v28
                                                                                                                                              = let v28
                                                                                                                                                      = coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                          v23 in
                                                                                                                                                coe
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                     v22
                                                                                                                                                     v20
                                                                                                                                                     v28
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                        (coe
                                                                                                                                                           v5)
                                                                                                                                                        (coe
                                                                                                                                                           v22))) in
                                                                                                                                        coe
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                             v27
                                                                                                                                             v26
                                                                                                                                             v28
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                (coe
                                                                                                                                                   v5)
                                                                                                                                                (coe
                                                                                                                                                   v27)))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                      -> let v19
                                                                                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                   (coe
                                                                                                                      v5)
                                                                                                                   (coe
                                                                                                                      v0) in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v19 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                                -> case coe
                                                                                                                          v20 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                       -> let v23
                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                    (coe
                                                                                                                                       v5)
                                                                                                                                    (coe
                                                                                                                                       v21)
                                                                                                                                    (coe
                                                                                                                                       v22) in
                                                                                                                          coe
                                                                                                                            (case coe
                                                                                                                                    v23 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                                 -> case coe
                                                                                                                                           v24 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                        -> let v27
                                                                                                                                                 = let v27
                                                                                                                                                         = coe
                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                             (coe
                                                                                                                                                                v5)
                                                                                                                                                             (coe
                                                                                                                                                                v0) in
                                                                                                                                                   coe
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                        v22
                                                                                                                                                        v21
                                                                                                                                                        v27
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                           (coe
                                                                                                                                                              v5)
                                                                                                                                                           (coe
                                                                                                                                                              v22))) in
                                                                                                                                           coe
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                v26
                                                                                                                                                v25
                                                                                                                                                v27
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                   (coe
                                                                                                                                                      v5)
                                                                                                                                                   (coe
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> case coe
                                                                                                                          v19 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                                       -> case coe
                                                                                                                                 v20 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                   v22
                                                                                                                                   v21
                                                                                                                                   erased
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                      (coe
                                                                                                                                         v5)
                                                                                                                                      (coe
                                                                                                                                         v22))
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                                       coe
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                            v17 v16
                                                                                            v18
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                               (coe
                                                                                                  v5)
                                                                                               (coe
                                                                                                  v17)))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> case coe v10 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                            -> case coe v11 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                   -> let v14
                                                                            = MAlonzo.Code.Once.Parser.Generic.Parser.d_sumTailP_86
                                                                                (coe v6) (coe v12)
                                                                                (coe v13) in
                                                                      coe
                                                                        (case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                             -> case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                    -> let v18
                                                                                             = let v18
                                                                                                     = coe
                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                                         v5
                                                                                                         v0 in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v18 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                      -> case coe
                                                                                                                v19 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                             -> case coe
                                                                                                                       v21 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                    -> let v24
                                                                                                                             = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                 (coe
                                                                                                                                    v5)
                                                                                                                                 (coe
                                                                                                                                    v20)
                                                                                                                                 (coe
                                                                                                                                    v22) in
                                                                                                                       coe
                                                                                                                         (case coe
                                                                                                                                 v24 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
                                                                                                                              -> case coe
                                                                                                                                        v25 of
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                     -> let v28
                                                                                                                                              = let v28
                                                                                                                                                      = coe
                                                                                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                          v23 in
                                                                                                                                                coe
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                     v22
                                                                                                                                                     v20
                                                                                                                                                     v28
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                        (coe
                                                                                                                                                           v5)
                                                                                                                                                        (coe
                                                                                                                                                           v22))) in
                                                                                                                                        coe
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                             v27
                                                                                                                                             v26
                                                                                                                                             v28
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                (coe
                                                                                                                                                   v5)
                                                                                                                                                (coe
                                                                                                                                                   v27)))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                      -> let v19
                                                                                                               = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                                   (coe
                                                                                                                      v5)
                                                                                                                   (coe
                                                                                                                      v0) in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v19 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                                -> case coe
                                                                                                                          v20 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                       -> let v23
                                                                                                                                = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                                    (coe
                                                                                                                                       v5)
                                                                                                                                    (coe
                                                                                                                                       v21)
                                                                                                                                    (coe
                                                                                                                                       v22) in
                                                                                                                          coe
                                                                                                                            (case coe
                                                                                                                                    v23 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                                                                                                                                 -> case coe
                                                                                                                                           v24 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                        -> let v27
                                                                                                                                                 = let v27
                                                                                                                                                         = coe
                                                                                                                                                             MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                             (coe
                                                                                                                                                                v5)
                                                                                                                                                             (coe
                                                                                                                                                                v0) in
                                                                                                                                                   coe
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                                        v22
                                                                                                                                                        v21
                                                                                                                                                        v27
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                           (coe
                                                                                                                                                              v5)
                                                                                                                                                           (coe
                                                                                                                                                              v22))) in
                                                                                                                                           coe
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                                v26
                                                                                                                                                v25
                                                                                                                                                v27
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                                   (coe
                                                                                                                                                      v5)
                                                                                                                                                   (coe
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> case coe
                                                                                                                          v19 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                                       -> case coe
                                                                                                                                 v20 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                   v22
                                                                                                                                   v21
                                                                                                                                   erased
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                      (coe
                                                                                                                                         v5)
                                                                                                                                      (coe
                                                                                                                                         v22))
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                                       coe
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                            v17 v16
                                                                                            v18
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                               (coe
                                                                                                  v5)
                                                                                               (coe
                                                                                                  v17)))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                                   -> case coe v11 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                          -> let v14
                                                                                   = let v14
                                                                                           = coe
                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200
                                                                                               v5
                                                                                               v0 in
                                                                                     coe
                                                                                       (case coe
                                                                                               v14 of
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                                            -> case coe
                                                                                                      v15 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                                   -> case coe
                                                                                                             v17 of
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                                          -> let v20
                                                                                                                   = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                       (coe
                                                                                                                          v5)
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
                                                                                                                           -> let v24
                                                                                                                                    = let v24
                                                                                                                                            = coe
                                                                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.C_pa'45'extra_446
                                                                                                                                                v19 in
                                                                                                                                      coe
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                           v18
                                                                                                                                           v16
                                                                                                                                           v24
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                              (coe
                                                                                                                                                 v5)
                                                                                                                                              (coe
                                                                                                                                                 v18))) in
                                                                                                                              coe
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                   v23
                                                                                                                                   v22
                                                                                                                                   v24
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                      (coe
                                                                                                                                         v5)
                                                                                                                                      (coe
                                                                                                                                         v23)))
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                            -> let v15
                                                                                                     = MAlonzo.Code.Once.Parser.Generic.Parser.d_atomKw_100
                                                                                                         (coe
                                                                                                            v5)
                                                                                                         (coe
                                                                                                            v0) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v15 of
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                      -> case coe
                                                                                                                v16 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                             -> let v19
                                                                                                                      = MAlonzo.Code.Once.Parser.Generic.Parser.d_prodTailP_84
                                                                                                                          (coe
                                                                                                                             v5)
                                                                                                                          (coe
                                                                                                                             v17)
                                                                                                                          (coe
                                                                                                                             v18) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v19 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                                       -> case coe
                                                                                                                                 v20 of
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                              -> let v23
                                                                                                                                       = let v23
                                                                                                                                               = coe
                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'kw_316
                                                                                                                                                   (coe
                                                                                                                                                      v5)
                                                                                                                                                   (coe
                                                                                                                                                      v0) in
                                                                                                                                         coe
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Once.Parser.Generic.Relation.C_pp'45'mk_468
                                                                                                                                              v18
                                                                                                                                              v17
                                                                                                                                              v23
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'prodTail_338
                                                                                                                                                 (coe
                                                                                                                                                    v5)
                                                                                                                                                 (coe
                                                                                                                                                    v18))) in
                                                                                                                                 coe
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                                      v22
                                                                                                                                      v21
                                                                                                                                      v23
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                                         (coe
                                                                                                                                            v5)
                                                                                                                                         (coe
                                                                                                                                            v22)))
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                      -> case coe
                                                                                                                v15 of
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                             -> case coe
                                                                                                                       v16 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                                    -> coe
                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.C_ps'45'mk_500
                                                                                                                         v18
                                                                                                                         v17
                                                                                                                         erased
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'sumTail_360
                                                                                                                            (coe
                                                                                                                               v5)
                                                                                                                            (coe
                                                                                                                               v18))
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError) in
                                                                             coe
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.C_pt'45'mk_532
                                                                                  v13 v12 v14
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'arrowTail_382
                                                                                     (coe v5)
                                                                                     (coe v13)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError)))))))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.PolyTypeBridge.parsePolyTypeB-complete
d_parsePolyTypeB'45'complete_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyTypeB'45'complete_100 v0 ~v1 ~v2 ~v3
  = du_parsePolyTypeB'45'complete_100 v0
du_parsePolyTypeB'45'complete_100 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parsePolyTypeB'45'complete_100 v0
  = coe
      du_ppB'45'go'45'complete_60 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_82
         (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
         (coe v0))
