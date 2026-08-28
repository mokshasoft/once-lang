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

module MAlonzo.Code.Once.Parser.PolyType where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Generic.Parser
import qualified MAlonzo.Code.Once.Parser.Generic.PolyInst
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Generic.Sound
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.PolyType.PolyParser
d_PolyParser_6 :: () -> ()
d_PolyParser_6 = erased
-- Once.Parser.PolyType.pkOf
d_pkOf_10 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pkOf_10 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Type.C_PK_242 (coe v2)) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyType.pmuOf
d_pmuOf_16 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pmuOf_16 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Type.C_Pμ'45'type_262 (coe v2)) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyType.parsePolyTypeImpl
d_parsePolyTypeImpl_22 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyTypeImpl_22 v0
  = let v1 = d_parsePolySumImpl_24 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parsePolyArrowTail_30 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PolyType.parsePolySumImpl
d_parsePolySumImpl_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolySumImpl_24 v0
  = let v1 = d_parsePolyProdImpl_26 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parsePolySumTail_32 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PolyType.parsePolyProdImpl
d_parsePolyProdImpl_26 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyProdImpl_26 v0
  = let v1 = d_parsePolyAtomImpl_28 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parsePolyProdTail_34 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PolyType.parsePolyAtomImpl
d_parsePolyAtomImpl_28 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyAtomImpl_28 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                               (coe ("Unit" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Type.C_PUnit_250) (coe v2)))
                              else coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v7 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v3) (coe ("Void" :: Data.Text.Text))) in
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
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_PVoid_252)
                                                               (coe v2)))
                                                  else coe
                                                         seq (coe v9)
                                                         (let v10
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                    erased
                                                                    (\ v10 ->
                                                                       coe
                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                         (coe v3))
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                       (coe v3)
                                                                       (coe
                                                                          ("Int"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                 -> if coe v11
                                                                      then coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.C_PInt_266)
                                                                                   (coe v2)))
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (let v13
                                                                                    = coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                        erased
                                                                                        (\ v13 ->
                                                                                           coe
                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                             (coe
                                                                                                v3))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                           (coe v3)
                                                                                           (coe
                                                                                              ("Float"
                                                                                               ::
                                                                                               Data.Text.Text))) in
                                                                              coe
                                                                                (case coe v13 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                     -> if coe v14
                                                                                          then coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Type.C_PFloat_268)
                                                                                                       (coe
                                                                                                          v2)))
                                                                                          else coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (let v16
                                                                                                        = coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                            erased
                                                                                                            (\ v16 ->
                                                                                                               coe
                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                 (coe
                                                                                                                    v3))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                               (coe
                                                                                                                  v3)
                                                                                                               (coe
                                                                                                                  ("Buffer"
                                                                                                                   ::
                                                                                                                   Data.Text.Text))) in
                                                                                                  coe
                                                                                                    (case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                         -> if coe
                                                                                                                 v17
                                                                                                              then coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C_PBuffer_272)
                                                                                                                           (coe
                                                                                                                              v2)))
                                                                                                              else coe
                                                                                                                     seq
                                                                                                                     (coe
                                                                                                                        v18)
                                                                                                                     (let v19
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                erased
                                                                                                                                (\ v19 ->
                                                                                                                                   coe
                                                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                     (coe
                                                                                                                                        v3))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                   (coe
                                                                                                                                      v3)
                                                                                                                                   (coe
                                                                                                                                      ("String"
                                                                                                                                       ::
                                                                                                                                       Data.Text.Text))) in
                                                                                                                      coe
                                                                                                                        (case coe
                                                                                                                                v19 of
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                             -> if coe
                                                                                                                                     v20
                                                                                                                                  then coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v21)
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Type.C_PStr_270)
                                                                                                                                               (coe
                                                                                                                                                  v2)))
                                                                                                                                  else coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v21)
                                                                                                                                         (let v22
                                                                                                                                                = coe
                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                    erased
                                                                                                                                                    (\ v22 ->
                                                                                                                                                       coe
                                                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                         (coe
                                                                                                                                                            v3))
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                       (coe
                                                                                                                                                          v3)
                                                                                                                                                       (coe
                                                                                                                                                          ("Eff"
                                                                                                                                                           ::
                                                                                                                                                           Data.Text.Text))) in
                                                                                                                                          coe
                                                                                                                                            (case coe
                                                                                                                                                    v22 of
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                 -> if coe
                                                                                                                                                         v23
                                                                                                                                                      then coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v24)
                                                                                                                                                             (let v25
                                                                                                                                                                    = d_parsePolyAtomImpl_28
                                                                                                                                                                        (coe
                                                                                                                                                                           v2) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v25 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v26 of
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                                                            -> let v29
                                                                                                                                                                                     = d_parsePolyAtomImpl_28
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v28) in
                                                                                                                                                                               coe
                                                                                                                                                                                 (case coe
                                                                                                                                                                                         v29 of
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                                                                      -> case coe
                                                                                                                                                                                                v30 of
                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                                                             -> coe
                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Once.Type.C_PEff_260
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v27)
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v31))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v32))
                                                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                      -> coe
                                                                                                                                                                                           v29
                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                     -> coe
                                                                                                                                                                          v25
                                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                      else coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v24)
                                                                                                                                                             (let v25
                                                                                                                                                                    = coe
                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                        erased
                                                                                                                                                                        (\ v25 ->
                                                                                                                                                                           coe
                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                             (coe
                                                                                                                                                                                v3))
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                           (coe
                                                                                                                                                                              v3)
                                                                                                                                                                           (coe
                                                                                                                                                                              ("IO"
                                                                                                                                                                               ::
                                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v25 of
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                                                     -> if coe
                                                                                                                                                                             v26
                                                                                                                                                                          then coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v27)
                                                                                                                                                                                 (let v28
                                                                                                                                                                                        = d_parsePolyAtomImpl_28
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v2) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v28 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v29 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                                                                -> coe
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           MAlonzo.Code.Once.Type.C_PEff_260
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Once.Type.C_PUnit_250)
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              v30))
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v31))
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                         -> coe
                                                                                                                                                                                              v28
                                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                          else coe
                                                                                                                                                                                 seq
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v27)
                                                                                                                                                                                 (let v28
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                            erased
                                                                                                                                                                                            (\ v28 ->
                                                                                                                                                                                               coe
                                                                                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    v3))
                                                                                                                                                                                            (coe
                                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v3)
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  ("Mu"
                                                                                                                                                                                                   ::
                                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v28 of
                                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                                                         -> if coe
                                                                                                                                                                                                 v29
                                                                                                                                                                                              then coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v30)
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        d_pmuOf_16
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           d_parsePolyFuncAtom_40
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              v2)))
                                                                                                                                                                                              else coe
                                                                                                                                                                                                     seq
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        v30)
                                                                                                                                                                                                     (let v31
                                                                                                                                                                                                            = coe
                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                                                                                                                                                                v3 in
                                                                                                                                                                                                      coe
                                                                                                                                                                                                        (case coe
                                                                                                                                                                                                                v31 of
                                                                                                                                                                                                           []
                                                                                                                                                                                                             -> coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                                                                           (:) v32 v33
                                                                                                                                                                                                             -> let v34
                                                                                                                                                                                                                      = coe
                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Char.d_primIsLower_8
                                                                                                                                                                                                                          v32 in
                                                                                                                                                                                                                coe
                                                                                                                                                                                                                  (if coe
                                                                                                                                                                                                                        v34
                                                                                                                                                                                                                     then coe
                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  MAlonzo.Code.Once.Type.C_PTVar_274
                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                     v3))
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  v2))
                                                                                                                                                                                                                     else coe
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
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v3 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> let v3 = d_parsePolyAtomImpl_28 (coe v2) in
                  coe
                    (case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = d_parsePolyProdTail_34 (coe v5) (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> let v11
                                                          = d_parsePolySumTail_32
                                                              (coe v9) (coe v10) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                           -> case coe v12 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                  -> let v15
                                                                           = d_parsePolyArrowTail_30
                                                                               (coe v13)
                                                                               (coe v14) in
                                                                     coe
                                                                       (case coe v15 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                            -> case coe v16 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                   -> case coe
                                                                                             v18 of
                                                                                        (:) v19 v20
                                                                                          -> case coe
                                                                                                    v19 of
                                                                                               MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                                                 -> coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            v17)
                                                                                                         (coe
                                                                                                            v20))
                                                                                               _ -> coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                        _ -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
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
                                                                         -> case coe v14 of
                                                                              (:) v15 v16
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  v16))
                                                                                     _ -> coe v11
                                                                              _ -> coe v11
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
                                                                 = d_parsePolyArrowTail_30
                                                                     (coe v9) (coe v10) in
                                                           coe
                                                             (case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                  -> case coe v12 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                         -> case coe v14 of
                                                                              (:) v15 v16
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  v16))
                                                                                     _ -> coe v7
                                                                              _ -> coe v7
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
                                                               -> case coe v10 of
                                                                    (:) v11 v12
                                                                      -> case coe v11 of
                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v9)
                                                                                     (coe v12))
                                                                           _ -> coe v7
                                                                    _ -> coe v7
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v7
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                       -> let v7 = d_parsePolySumTail_32 (coe v5) (coe v6) in
                                          coe
                                            (case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                        -> let v11
                                                                 = d_parsePolyArrowTail_30
                                                                     (coe v9) (coe v10) in
                                                           coe
                                                             (case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                  -> case coe v12 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                         -> case coe v14 of
                                                                              (:) v15 v16
                                                                                -> case coe v15 of
                                                                                     MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                                       -> coe
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v13)
                                                                                               (coe
                                                                                                  v16))
                                                                                     _ -> coe v3
                                                                              _ -> coe v3
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
                                                               -> case coe v10 of
                                                                    (:) v11 v12
                                                                      -> case coe v11 of
                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v9)
                                                                                     (coe v12))
                                                                           _ -> coe v7
                                                                    _ -> coe v7
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v7
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v3 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                       -> case coe v4 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                              -> let v7
                                                       = d_parsePolyArrowTail_30
                                                           (coe v5) (coe v6) in
                                                 coe
                                                   (case coe v7 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                        -> case coe v8 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                               -> case coe v10 of
                                                                    (:) v11 v12
                                                                      -> case coe v11 of
                                                                           MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v9)
                                                                                     (coe v12))
                                                                           _ -> coe v3
                                                                    _ -> coe v3
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v7
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> case coe v3 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                              -> case coe v4 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                                     -> case coe v6 of
                                                          (:) v7 v8
                                                            -> case coe v7 of
                                                                 MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                   -> coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v5) (coe v8))
                                                                 _ -> coe v3
                                                          _ -> coe v3
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyType.parsePolyArrowTail
d_parsePolyArrowTail_30 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyArrowTail_30 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                  -> let v5 = d_parsePolySumImpl_24 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> let v9 = d_parsePolyArrowTail_30 (coe v7) (coe v8) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                             -> case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                               (coe v0)
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe v11))
                                                            (coe v12))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                     (coe v0) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v7))
                                                  (coe v8))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
                  -> case coe v4 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = d_parsePolySumImpl_24 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> let v11
                                                          = d_parsePolyArrowTail_30
                                                              (coe v9) (coe v10) in
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
                                                                             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_One_8)
                                                                             (coe v13))
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
                                                                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_One_8)
                                                                   (coe v9))
                                                                (coe v10))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v2
                       _ -> coe v2
                MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
                  -> case coe v4 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = d_parsePolySumImpl_24 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> let v11
                                                          = d_parsePolyArrowTail_30
                                                              (coe v9) (coe v10) in
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
                                                                             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Zero_6)
                                                                             (coe v13))
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
                                                                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Zero_6)
                                                                   (coe v9))
                                                                (coe v10))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v2
                       _ -> coe v2
                MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
                  -> case coe v4 of
                       (:) v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Parser.Token.C_TArrow_28
                                -> let v7 = d_parsePolySumImpl_24 (coe v6) in
                                   coe
                                     (case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> let v11
                                                          = d_parsePolyArrowTail_30
                                                              (coe v9) (coe v10) in
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
                                                                             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                             (coe v0)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Many_10)
                                                                             (coe v13))
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
                                                                   MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
                                                                   (coe v0)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10)
                                                                   (coe v9))
                                                                (coe v10))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v7
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v2
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.PolyType.parsePolySumTail
d_parsePolySumTail_32 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolySumTail_32 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TPlus_48
                  -> let v5 = d_parsePolyProdImpl_26 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        d_parsePolySumTail_32
                                        (coe MAlonzo.Code.Once.Type.C__P'43'__256 (coe v0) (coe v7))
                                        (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.PolyType.parsePolyProdTail
d_parsePolyProdTail_34 ::
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyProdTail_34 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TStar_52
                  -> let v5 = d_parsePolyAtomImpl_28 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        d_parsePolyProdTail_34
                                        (coe MAlonzo.Code.Once.Type.C__P'42'__254 (coe v0) (coe v7))
                                        (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.PolyType.parsePolyFuncSum
d_parsePolyFuncSum_36 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyFuncSum_36 v0
  = let v1 = d_parsePolyFuncProd_38 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parsePolyFuncSumTail_42 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PolyType.parsePolyFuncProd
d_parsePolyFuncProd_38 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyFuncProd_38 v0
  = let v1 = d_parsePolyFuncAtom_40 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe d_parsePolyFuncProdTail_44 (coe v3) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PolyType.parsePolyFuncAtom
d_parsePolyFuncAtom_40 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyFuncAtom_40 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> let v5
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe ("Id" :: Data.Text.Text))) in
                     coe
                       (let v6
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v6 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v4))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                     (coe ("K" :: Data.Text.Text))) in
                        coe
                          (case coe v5 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe MAlonzo.Code.Once.Type.C_PId_244) (coe v3)))
                                    else coe
                                           seq (coe v8)
                                           (case coe v6 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                -> if coe v9
                                                     then coe
                                                            seq (coe v10)
                                                            (coe
                                                               d_pkOf_10
                                                               (coe
                                                                  d_parsePolyAtomImpl_28 (coe v3)))
                                                     else coe
                                                            seq (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> let v4 = d_parsePolyFuncAtom_40 (coe v3) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> let v8 = d_parsePolyFuncProdTail_44 (coe v6) (coe v7) in
                                      coe
                                        (case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                    -> let v12
                                                             = d_parsePolyFuncSumTail_42
                                                                 (coe v10) (coe v11) in
                                                       coe
                                                         (case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                              -> case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                     -> case coe v15 of
                                                                          (:) v16 v17
                                                                            -> case coe v16 of
                                                                                 MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v14)
                                                                                           (coe
                                                                                              v17))
                                                                                 _ -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                          _ -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
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
                                                           -> case coe v11 of
                                                                (:) v12 v13
                                                                  -> case coe v12 of
                                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                         -> coe
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe v10)
                                                                                 (coe v13))
                                                                       _ -> coe v8
                                                                _ -> coe v8
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v8
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                   -> case coe v5 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                          -> let v8 = d_parsePolyFuncSumTail_42 (coe v6) (coe v7) in
                                             coe
                                               (case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                           -> case coe v11 of
                                                                (:) v12 v13
                                                                  -> case coe v12 of
                                                                       MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                                         -> coe
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe v10)
                                                                                 (coe v13))
                                                                       _ -> coe v4
                                                                _ -> coe v4
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v8
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v4 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                          -> case coe v5 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                                 -> case coe v7 of
                                                      (:) v8 v9
                                                        -> case coe v8 of
                                                             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v6) (coe v9))
                                                             _ -> coe v4
                                                      _ -> coe v4
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.PolyType.parsePolyFuncSumTail
d_parsePolyFuncSumTail_42 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyFuncSumTail_42 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TPlus_48
                  -> let v5 = d_parsePolyFuncProd_38 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        d_parsePolyFuncSumTail_42
                                        (coe
                                           MAlonzo.Code.Once.Type.C__P'8853'__246 (coe v0) (coe v7))
                                        (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.PolyType.parsePolyFuncProdTail
d_parsePolyFuncProdTail_44 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_238 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyFuncProdTail_44 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TStar_52
                  -> let v5 = d_parsePolyFuncAtom_40 (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        d_parsePolyFuncProdTail_44
                                        (coe
                                           MAlonzo.Code.Once.Type.C__P'8855'__248 (coe v0) (coe v7))
                                        (coe v8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.PolyType.parsePolyType
d_parsePolyType_528 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyType_528 = coe d_parsePolyTypeImpl_22
-- Once.Parser.PolyType.ParsePolyAtB
d_ParsePolyAtB_530 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParsePolyAtB_530 = erased
-- Once.Parser.PolyType.ppB-go
d_ppB'45'go_542 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ppB'45'go_542 v0 v1 ~v2 = du_ppB'45'go_542 v0 v1
du_ppB'45'go_542 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ppB'45'go_542 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Once.Parser.Generic.Relation.du_typeShrink_708
                             (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
                             (coe v0) (coe v4)
                             (coe
                                MAlonzo.Code.Once.Parser.Generic.Sound.du_sound'45'type_370
                                (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
                                (coe v0)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyType.parsePolyTypeB
d_parsePolyTypeB_558 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePolyTypeB_558 v0
  = coe
      du_ppB'45'go_542 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Parser.d_typeP_82
         (coe MAlonzo.Code.Once.Parser.Generic.PolyInst.d_PolyAlg_118)
         (coe v0))
