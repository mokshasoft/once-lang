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

module MAlonzo.Code.Once.Parser.Generic.Parser where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Generic.Parser.effHead?
d_effHead'63'_12 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_effHead'63'_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> case coe v3 of
                       (:) v4 v5
                         -> case coe v4 of
                              MAlonzo.Code.Once.Parser.Token.C_TWord_8 v6
                                -> let v7
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                             erased
                                             (\ v7 ->
                                                coe
                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                  (coe v6))
                                             (coe
                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                (coe v6) (coe ("Eff" :: Data.Text.Text))) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> if coe v8
                                               then coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v5) erased))
                                               else coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Parser.Make.atomP
d_atomP_104 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_104 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe d_atomKw_128 (coe v0) (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.prodP
d_prodP_106 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_106 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe d_prodTailP_112 (coe v0) (coe v4) (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3 = d_atomKw_128 (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> coe d_prodTailP_112 (coe v0) (coe v5) (coe v6)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.sumP
d_sumP_108 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_108 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8 = d_prodTailP_112 (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> coe d_sumTailP_114 (coe v0) (coe v10) (coe v11)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3 = d_atomKw_128 (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7 = d_prodTailP_112 (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> coe d_sumTailP_114 (coe v0) (coe v9) (coe v10)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> coe d_sumTailP_114 (coe v0) (coe v5) (coe v6)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.typeP
d_typeP_110 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_110 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8 = d_prodTailP_112 (coe v0) (coe v4) (coe v6) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> let v12
                                                   = d_sumTailP_114 (coe v0) (coe v10) (coe v11) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                    -> case coe v13 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                           -> coe
                                                                d_arrowTailP_116 (coe v0) (coe v14)
                                                                (coe v15)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v12
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> coe
                                                      d_arrowTailP_116 (coe v0) (coe v10) (coe v11)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v3 = d_atomKw_128 (coe v0) (coe v1) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> let v7 = d_prodTailP_112 (coe v0) (coe v5) (coe v6) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = d_sumTailP_114
                                                          (coe v0) (coe v9) (coe v10) in
                                                coe
                                                  (case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> coe
                                                                   d_arrowTailP_116 (coe v0)
                                                                   (coe v13) (coe v14)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         d_arrowTailP_116 (coe v0) (coe v9)
                                                         (coe v10)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> let v7 = d_sumTailP_114 (coe v0) (coe v5) (coe v6) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> coe
                                                         d_arrowTailP_116 (coe v0) (coe v9)
                                                         (coe v10)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                   -> case coe v4 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                          -> coe d_arrowTailP_116 (coe v0) (coe v5) (coe v6)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.prodTailP
d_prodTailP_112 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_112 v0 v1 v2
  = coe
      du_ptGo_414 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
-- Once.Parser.Generic.Parser.Make.sumTailP
d_sumTailP_114 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_114 v0 v1 v2
  = coe
      du_stGo_462 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
-- Once.Parser.Generic.Parser.Make.arrowTailP
d_arrowTailP_116 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_116 v0 v1 v2
  = coe
      du_atGo_510 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_arrowDir_22 (coe v2))
-- Once.Parser.Generic.Parser.Make.fAtomP
d_fAtomP_118 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_118 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v5
                  -> let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v5))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                  (coe ("Id" :: Data.Text.Text))) in
                     coe
                       (let v7
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v5))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                     (coe ("K" :: Data.Text.Text))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                               -> if coe v8
                                    then coe
                                           seq (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_fId_190
                                                    (coe v0))
                                                 (coe v4)))
                                    else coe
                                           seq (coe v9)
                                           (case coe v7 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                -> if coe v10
                                                     then coe
                                                            seq (coe v11)
                                                            (let v12
                                                                   = coe
                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                       v0 v4 in
                                                             coe
                                                               (case coe v12 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                    -> case coe v13 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                           -> case coe v15 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_fK_188
                                                                                             v0 v14)
                                                                                          (coe v16))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v13
                                                                             = d_atomKw_128
                                                                                 (coe v0)
                                                                                 (coe v4) in
                                                                       coe
                                                                         (case coe v13 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                              -> case coe v14 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                     -> coe
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_fK_188
                                                                                                v0
                                                                                                v15)
                                                                                             (coe
                                                                                                v16))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe v13
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     else coe
                                                            seq (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> let v5 = d_fSumP_122 (coe v0) (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        (:) v9 v10
                                          -> case coe v9 of
                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v7) (coe v10))
                                               _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.Generic.Parser.Make.fProdP
d_fProdP_120 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_120 v0 v1
  = let v2 = d_fAtomP_118 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe d_fProdTailP_124 (coe v0) (coe v4) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.fSumP
d_fSumP_122 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_122 v0 v1
  = let v2 = d_fAtomP_118 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6 = d_fProdTailP_124 (coe v0) (coe v4) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> coe d_fSumTailP_126 (coe v0) (coe v8) (coe v9)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> coe d_fSumTailP_126 (coe v0) (coe v4) (coe v5)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Generic.Parser.Make.fProdTailP
d_fProdTailP_124 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_124 v0 v1 v2
  = coe
      du_fptGo_640 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
-- Once.Parser.Generic.Parser.Make.fSumTailP
d_fSumTailP_126 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_126 v0 v1 v2
  = coe
      du_fstGo_688 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
-- Once.Parser.Generic.Parser.Make.atomKw
d_atomKw_128 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_128 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v5
                  -> let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v5))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                  (coe ("Unit" :: Data.Text.Text))) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_aUnit_162
                                                 (coe v0))
                                              (coe v4)))
                                 else coe
                                        seq (coe v8)
                                        (let v9
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v9 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v5))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v5) (coe ("Void" :: Data.Text.Text))) in
                                         coe
                                           (case coe v9 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                -> if coe v10
                                                     then coe
                                                            seq (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_aVoid_164
                                                                     (coe v0))
                                                                  (coe v4)))
                                                     else coe
                                                            seq (coe v11)
                                                            (let v12
                                                                   = coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                       erased
                                                                       (\ v12 ->
                                                                          coe
                                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                            (coe v5))
                                                                       (coe
                                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                          (coe v5)
                                                                          (coe
                                                                             ("Int"
                                                                              ::
                                                                              Data.Text.Text))) in
                                                             coe
                                                               (case coe v12 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                    -> if coe v13
                                                                         then coe
                                                                                seq (coe v14)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_aInt_166
                                                                                         (coe v0))
                                                                                      (coe v4)))
                                                                         else coe
                                                                                seq (coe v14)
                                                                                (let v15
                                                                                       = coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                           erased
                                                                                           (\ v15 ->
                                                                                              coe
                                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                (coe
                                                                                                   v5))
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                              (coe
                                                                                                 v5)
                                                                                              (coe
                                                                                                 ("Float"
                                                                                                  ::
                                                                                                  Data.Text.Text))) in
                                                                                 coe
                                                                                   (case coe v15 of
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                        -> if coe
                                                                                                v16
                                                                                             then coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v17)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_aFloat_168
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             v4)))
                                                                                             else coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v17)
                                                                                                    (let v18
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                               erased
                                                                                                               (\ v18 ->
                                                                                                                  coe
                                                                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                    (coe
                                                                                                                       v5))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                  (coe
                                                                                                                     v5)
                                                                                                                  (coe
                                                                                                                     ("Buffer"
                                                                                                                      ::
                                                                                                                      Data.Text.Text))) in
                                                                                                     coe
                                                                                                       (case coe
                                                                                                               v18 of
                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                            -> if coe
                                                                                                                    v19
                                                                                                                 then coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v20)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_aBuffer_170
                                                                                                                                 (coe
                                                                                                                                    v0))
                                                                                                                              (coe
                                                                                                                                 v4)))
                                                                                                                 else coe
                                                                                                                        seq
                                                                                                                        (coe
                                                                                                                           v20)
                                                                                                                        (let v21
                                                                                                                               = coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                   erased
                                                                                                                                   (\ v21 ->
                                                                                                                                      coe
                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                        (coe
                                                                                                                                           v5))
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                      (coe
                                                                                                                                         v5)
                                                                                                                                      (coe
                                                                                                                                         ("String"
                                                                                                                                          ::
                                                                                                                                          Data.Text.Text))) in
                                                                                                                         coe
                                                                                                                           (case coe
                                                                                                                                   v21 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                -> if coe
                                                                                                                                        v22
                                                                                                                                     then coe
                                                                                                                                            seq
                                                                                                                                            (coe
                                                                                                                                               v23)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_aStr_172
                                                                                                                                                     (coe
                                                                                                                                                        v0))
                                                                                                                                                  (coe
                                                                                                                                                     v4)))
                                                                                                                                     else coe
                                                                                                                                            seq
                                                                                                                                            (coe
                                                                                                                                               v23)
                                                                                                                                            (let v24
                                                                                                                                                   = coe
                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                       erased
                                                                                                                                                       (\ v24 ->
                                                                                                                                                          coe
                                                                                                                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                            (coe
                                                                                                                                                               v5))
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                          (coe
                                                                                                                                                             v5)
                                                                                                                                                          (coe
                                                                                                                                                             ("Eff"
                                                                                                                                                              ::
                                                                                                                                                              Data.Text.Text))) in
                                                                                                                                             coe
                                                                                                                                               (case coe
                                                                                                                                                       v24 of
                                                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                                                                    -> if coe
                                                                                                                                                            v25
                                                                                                                                                         then coe
                                                                                                                                                                seq
                                                                                                                                                                (coe
                                                                                                                                                                   v26)
                                                                                                                                                                (let v27
                                                                                                                                                                       = coe
                                                                                                                                                                           MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                           v0
                                                                                                                                                                           v4 in
                                                                                                                                                                 coe
                                                                                                                                                                   (case coe
                                                                                                                                                                           v27 of
                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v28
                                                                                                                                                                        -> case coe
                                                                                                                                                                                  v28 of
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                                                               -> case coe
                                                                                                                                                                                         v30 of
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                      -> let v33
                                                                                                                                                                                               = coe
                                                                                                                                                                                                   MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                                   v0
                                                                                                                                                                                                   v31 in
                                                                                                                                                                                         coe
                                                                                                                                                                                           (case coe
                                                                                                                                                                                                   v33 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v34 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                       -> case coe
                                                                                                                                                                                                                 v36 of
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                                                                                                                              -> coe
                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                         v0
                                                                                                                                                                                                                         v29
                                                                                                                                                                                                                         v35)
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v37))
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                -> let v34
                                                                                                                                                                                                         = d_atomKw_128
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v0)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v31) in
                                                                                                                                                                                                   coe
                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                             v34 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v35
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v35 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                            v0
                                                                                                                                                                                                                            v29
                                                                                                                                                                                                                            v36)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v37))
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                          -> coe
                                                                                                                                                                                                               v34
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                        -> let v28
                                                                                                                                                                                 = d_atomKw_128
                                                                                                                                                                                     (coe
                                                                                                                                                                                        v0)
                                                                                                                                                                                     (coe
                                                                                                                                                                                        v4) in
                                                                                                                                                                           coe
                                                                                                                                                                             (case coe
                                                                                                                                                                                     v28 of
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                                                                  -> case coe
                                                                                                                                                                                            v29 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                                         -> let v32
                                                                                                                                                                                                  = coe
                                                                                                                                                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                                      v0
                                                                                                                                                                                                      v31 in
                                                                                                                                                                                            coe
                                                                                                                                                                                              (case coe
                                                                                                                                                                                                      v32 of
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                                                                                                   -> case coe
                                                                                                                                                                                                             v33 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                                    v35 of
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                            v0
                                                                                                                                                                                                                            v30
                                                                                                                                                                                                                            v34)
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            v36))
                                                                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                   -> let v33
                                                                                                                                                                                                            = d_atomKw_128
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   v0)
                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                   v31) in
                                                                                                                                                                                                      coe
                                                                                                                                                                                                        (case coe
                                                                                                                                                                                                                v33 of
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                             -> case coe
                                                                                                                                                                                                                       v34 of
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                    -> coe
                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                               v0
                                                                                                                                                                                                                               v30
                                                                                                                                                                                                                               v35)
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v36))
                                                                                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                             -> coe
                                                                                                                                                                                                                  v33
                                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                  -> coe
                                                                                                                                                                                       v28
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                         else coe
                                                                                                                                                                seq
                                                                                                                                                                (coe
                                                                                                                                                                   v26)
                                                                                                                                                                (let v27
                                                                                                                                                                       = coe
                                                                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                           erased
                                                                                                                                                                           (\ v27 ->
                                                                                                                                                                              coe
                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                (coe
                                                                                                                                                                                   v5))
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                              (coe
                                                                                                                                                                                 v5)
                                                                                                                                                                              (coe
                                                                                                                                                                                 ("IO"
                                                                                                                                                                                  ::
                                                                                                                                                                                  Data.Text.Text))) in
                                                                                                                                                                 coe
                                                                                                                                                                   (case coe
                                                                                                                                                                           v27 of
                                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                                                                                                                        -> if coe
                                                                                                                                                                                v28
                                                                                                                                                                             then coe
                                                                                                                                                                                    seq
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v29)
                                                                                                                                                                                    (let v30
                                                                                                                                                                                           = coe
                                                                                                                                                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212
                                                                                                                                                                                               v0
                                                                                                                                                                                               v4 in
                                                                                                                                                                                     coe
                                                                                                                                                                                       (case coe
                                                                                                                                                                                               v30 of
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v31
                                                                                                                                                                                            -> case coe
                                                                                                                                                                                                      v31 of
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                                                                   -> case coe
                                                                                                                                                                                                             v33 of
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                                                                                                                          -> coe
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                     v0
                                                                                                                                                                                                                     (MAlonzo.Code.Once.Parser.Generic.Relation.d_aUnit_162
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           v0))
                                                                                                                                                                                                                     v32)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v34))
                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                            -> let v31
                                                                                                                                                                                                     = d_atomKw_128
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            v0)
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            v4) in
                                                                                                                                                                                               coe
                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                         v31 of
                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                                                                                                      -> case coe
                                                                                                                                                                                                                v32 of
                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                                                                             -> coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_178
                                                                                                                                                                                                                        v0
                                                                                                                                                                                                                        (MAlonzo.Code.Once.Parser.Generic.Relation.d_aUnit_162
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              v0))
                                                                                                                                                                                                                        v33)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v34))
                                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                      -> coe
                                                                                                                                                                                                           v31
                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                             else coe
                                                                                                                                                                                    seq
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v29)
                                                                                                                                                                                    (let v30
                                                                                                                                                                                           = coe
                                                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                               erased
                                                                                                                                                                                               (\ v30 ->
                                                                                                                                                                                                  coe
                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       v5))
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     v5)
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     ("Mu"
                                                                                                                                                                                                      ::
                                                                                                                                                                                                      Data.Text.Text))) in
                                                                                                                                                                                     coe
                                                                                                                                                                                       (case coe
                                                                                                                                                                                               v30 of
                                                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                                                                                                            -> if coe
                                                                                                                                                                                                    v31
                                                                                                                                                                                                 then coe
                                                                                                                                                                                                        seq
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v32)
                                                                                                                                                                                                        (let v33
                                                                                                                                                                                                               = d_fSumP_122
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v0)
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v4) in
                                                                                                                                                                                                         coe
                                                                                                                                                                                                           (case coe
                                                                                                                                                                                                                   v33 of
                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v34
                                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                                          v34 of
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                                                                                                                                                       -> coe
                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_aMu_182
                                                                                                                                                                                                                                  v0
                                                                                                                                                                                                                                  v35)
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  v36))
                                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                                -> coe
                                                                                                                                                                                                                     v33
                                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                 else coe
                                                                                                                                                                                                        seq
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v32)
                                                                                                                                                                                                        (let v33
                                                                                                                                                                                                               = coe
                                                                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                   erased
                                                                                                                                                                                                                   (\ v33 ->
                                                                                                                                                                                                                      coe
                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           v5))
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v5)
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         ("Nu"
                                                                                                                                                                                                                          ::
                                                                                                                                                                                                                          Data.Text.Text))) in
                                                                                                                                                                                                         coe
                                                                                                                                                                                                           (case coe
                                                                                                                                                                                                                   v33 of
                                                                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                                                                                                                -> if coe
                                                                                                                                                                                                                        v34
                                                                                                                                                                                                                     then coe
                                                                                                                                                                                                                            seq
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v35)
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               d_nuP_130
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  v0)
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  v4))
                                                                                                                                                                                                                     else coe
                                                                                                                                                                                                                            seq
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               v35)
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> let v5 = d_typeP_110 (coe v0) (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        (:) v9 v10
                                          -> case coe v9 of
                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v7) (coe v10))
                                               _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.Generic.Parser.Make.nuP
d_nuP_130 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuP_130 v0 v1
  = coe
      d_nuTryP_134 (coe v0) (coe v1) (coe d_fSumP_122 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.nuEffP
d_nuEffP_132 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffP_132 v0 v1
  = coe du_nuEffWith_142 (coe v0) (coe d_effHead'63'_12 (coe v1))
-- Once.Parser.Generic.Parser.Make.nuTryP
d_nuTryP_134 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTryP_134 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aNu_184 v0 v4)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_nuEffP_132 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.nuCloseP
d_nuCloseP_136 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuCloseP_136 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                  coe
                    (case coe v4 of
                       (:) v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.d_aNuEff_186 v0
                                           v3)
                                        (coe v7))
                              _ -> coe v5
                       _ -> coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.nuEffWith
d_nuEffWith_142 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuEffWith_142 v0 ~v1 v2 = du_nuEffWith_142 v0 v2
du_nuEffWith_142 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_nuEffWith_142 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe d_nuCloseP_136 (coe v0) (coe d_fSumP_122 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make._.ptGo
d_ptGo_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptGo_414 v0 ~v1 ~v2 v3 v4 v5 = du_ptGo_414 v0 v3 v4 v5
du_ptGo_414 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ptGo_414 v0 v1 v2 v3
  = if coe v3
      then let v4
                 = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2) in
           coe
             (let v5
                    = coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                        (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                            -> case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                   -> coe
                                        d_prodTailP_112 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Parser.Generic.Relation.d_aProd_174 v0
                                           v1 v7)
                                        (coe v9)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v6 = d_atomKw_128 (coe v0) (coe v4) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> coe
                                           d_prodTailP_112 (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Parser.Generic.Relation.d_aProd_174
                                              v0 v1 v8)
                                           (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make._.stGo
d_stGo_462 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stGo_462 v0 ~v1 ~v2 v3 v4 v5 = du_stGo_462 v0 v3 v4 v5
du_stGo_462 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stGo_462 v0 v1 v2 v3
  = if coe v3
      then let v4
                 = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2) in
           coe
             (let v5
                    = coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                        (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                            -> case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                   -> let v11 = d_prodTailP_112 (coe v0) (coe v7) (coe v9) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                             -> case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                    -> coe
                                                         d_sumTailP_114 (coe v0)
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Generic.Relation.d_aSum_176
                                                            v0 v1 v13)
                                                         (coe v14)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v6 = d_atomKw_128 (coe v0) (coe v4) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10 = d_prodTailP_112 (coe v0) (coe v8) (coe v9) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> coe
                                                            d_sumTailP_114 (coe v0)
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Generic.Relation.d_aSum_176
                                                               v0 v1 v12)
                                                            (coe v13)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v10
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                             -> coe
                                                  d_sumTailP_114 (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Generic.Relation.d_aSum_176
                                                     v0 v1 v8)
                                                  (coe v9)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make._.atGo
d_atGo_510 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atGo_510 v0 ~v1 ~v2 v3 v4 v5 = du_atGo_510 v0 v3 v4 v5
du_atGo_510 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atGo_510 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adG_14 v4
        -> let v5
                 = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v2) in
           coe
             (let v6
                    = coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                        (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v2)) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> let v12 = d_prodTailP_112 (coe v0) (coe v8) (coe v10) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                    -> let v16
                                                             = d_sumTailP_114
                                                                 (coe v0) (coe v14) (coe v15) in
                                                       coe
                                                         (case coe v16 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                              -> case coe v17 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                     -> let v20
                                                                              = d_arrowTailP_116
                                                                                  (coe v0) (coe v18)
                                                                                  (coe v19) in
                                                                        coe
                                                                          (case coe v20 of
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                               -> case coe v21 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                      -> coe
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                                 v0
                                                                                                 v4
                                                                                                 v1
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v23))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                               -> coe v20
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> case coe v16 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                     -> case coe v17 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                       v0 v4 v1 v18)
                                                                                    (coe v19))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v16
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                    -> case coe v13 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                           -> let v16
                                                                    = d_arrowTailP_116
                                                                        (coe v0) (coe v14)
                                                                        (coe v15) in
                                                              coe
                                                                (case coe v16 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                     -> case coe v17 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                       v0 v4 v1 v18)
                                                                                    (coe v19))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v16
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v12 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                           -> case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                             v0 v4 v1 v14)
                                                                          (coe v15))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                           -> coe v12
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v7 = d_atomKw_128 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11 = d_prodTailP_112 (coe v0) (coe v9) (coe v10) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> let v15
                                                                = d_sumTailP_114
                                                                    (coe v0) (coe v13) (coe v14) in
                                                          coe
                                                            (case coe v15 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                 -> case coe v16 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                        -> let v19
                                                                                 = d_arrowTailP_116
                                                                                     (coe v0)
                                                                                     (coe v17)
                                                                                     (coe v18) in
                                                                           coe
                                                                             (case coe v19 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                  -> case coe v20 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                         -> coe
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                                    v0
                                                                                                    v4
                                                                                                    v1
                                                                                                    v21)
                                                                                                 (coe
                                                                                                    v22))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                  -> coe v19
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0 v4 v1
                                                                                          v17)
                                                                                       (coe v18))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v15
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> let v15
                                                                       = d_arrowTailP_116
                                                                           (coe v0) (coe v13)
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0 v4 v1
                                                                                          v17)
                                                                                       (coe v18))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v15
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0 v4 v1 v13)
                                                                             (coe v14))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v11
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> let v11
                                                      = d_sumTailP_114
                                                          (coe v0) (coe v9) (coe v10) in
                                                coe
                                                  (case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> let v15
                                                                       = d_arrowTailP_116
                                                                           (coe v0) (coe v13)
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0 v4 v1
                                                                                          v17)
                                                                                       (coe v18))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v15
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0 v4 v1 v13)
                                                                             (coe v14))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v11
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                    -> let v11
                                                             = d_arrowTailP_116
                                                                 (coe v0) (coe v9) (coe v10) in
                                                       coe
                                                         (case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0 v4 v1 v13)
                                                                             (coe v14))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v11
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v7 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                    -> case coe v8 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                      v0 v4 v1 v9)
                                                                   (coe v10))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v7
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adA_16
        -> let v4
                 = MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2) in
           coe
             (let v5
                    = coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_212 v0
                        (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                            -> case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                   -> let v11 = d_prodTailP_112 (coe v0) (coe v7) (coe v9) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                             -> case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                    -> let v15
                                                             = d_sumTailP_114
                                                                 (coe v0) (coe v13) (coe v14) in
                                                       coe
                                                         (case coe v15 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                              -> case coe v16 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                     -> let v19
                                                                              = d_arrowTailP_116
                                                                                  (coe v0) (coe v17)
                                                                                  (coe v18) in
                                                                        coe
                                                                          (case coe v19 of
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                               -> case coe v20 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                      -> coe
                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                                 v0
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                 v1
                                                                                                 v21)
                                                                                              (coe
                                                                                                 v22))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                               -> coe v19
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                       v0
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                                       v1 v17)
                                                                                    (coe v18))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v15
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v11 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                    -> case coe v12 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                           -> let v15
                                                                    = d_arrowTailP_116
                                                                        (coe v0) (coe v13)
                                                                        (coe v14) in
                                                              coe
                                                                (case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                       v0
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                                       v1 v17)
                                                                                    (coe v18))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v15
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                           -> case coe v12 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Many_10)
                                                                             v1 v13)
                                                                          (coe v14))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                           -> coe v11
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> let v6 = d_atomKw_128 (coe v0) (coe v4) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10 = d_prodTailP_112 (coe v0) (coe v8) (coe v9) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14
                                                                = d_sumTailP_114
                                                                    (coe v0) (coe v12) (coe v13) in
                                                          coe
                                                            (case coe v14 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                 -> case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                        -> let v18
                                                                                 = d_arrowTailP_116
                                                                                     (coe v0)
                                                                                     (coe v16)
                                                                                     (coe v17) in
                                                                           coe
                                                                             (case coe v18 of
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                  -> case coe v19 of
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                         -> coe
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                                    v0
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                    v1
                                                                                                    v20)
                                                                                                 (coe
                                                                                                    v21))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                  -> coe v18
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C_Many_10)
                                                                                          v1 v16)
                                                                                       (coe v17))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v14
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> case coe v10 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                              -> let v14
                                                                       = d_arrowTailP_116
                                                                           (coe v0) (coe v12)
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C_Many_10)
                                                                                          v1 v16)
                                                                                       (coe v17))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v14
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                              -> case coe v11 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                                v1 v12)
                                                                             (coe v13))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v10
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                             -> let v10
                                                      = d_sumTailP_114 (coe v0) (coe v8) (coe v9) in
                                                coe
                                                  (case coe v10 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                              -> let v14
                                                                       = d_arrowTailP_116
                                                                           (coe v0) (coe v12)
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                          v0
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Type.C_Many_10)
                                                                                          v1 v16)
                                                                                       (coe v17))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v14
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                              -> case coe v11 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                                v1 v12)
                                                                             (coe v13))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v10
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> case coe v6 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                             -> case coe v7 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                    -> let v10
                                                             = d_arrowTailP_116
                                                                 (coe v0) (coe v8) (coe v9) in
                                                       coe
                                                         (case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                              -> case coe v11 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                                v0
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                                v1 v12)
                                                                             (coe v13))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v10
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v6 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                                    -> case coe v7 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_180
                                                                      v0
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      v1 v8)
                                                                   (coe v9))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v6
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adR_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make._.fptGo
d_fptGo_640 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptGo_640 v0 ~v1 ~v2 v3 v4 v5 = du_fptGo_640 v0 v3 v4 v5
du_fptGo_640 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fptGo_640 v0 v1 v2 v3
  = if coe v3
      then let v4
                 = d_fAtomP_118
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              d_fProdTailP_124 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Parser.Generic.Relation.d_fProd_194 v0 v1 v6)
                              (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make._.fstGo
d_fstGo_688 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstGo_688 v0 ~v1 ~v2 v3 v4 v5 = du_fstGo_688 v0 v3 v4 v5
du_fstGo_688 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fstGo_688 v0 v1 v2 v3
  = if coe v3
      then let v4
                 = d_fAtomP_118
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> let v8 = d_fProdTailP_124 (coe v0) (coe v6) (coe v7) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> coe
                                               d_fSumTailP_126 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Parser.Generic.Relation.d_fSum_192
                                                  v0 v1 v10)
                                               (coe v11)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> coe
                                     d_fSumTailP_126 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Parser.Generic.Relation.d_fSum_192 v0 v1
                                        v6)
                                     (coe v7)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
