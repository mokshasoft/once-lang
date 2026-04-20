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

module MAlonzo.Code.Once.Parser.Module.DeclTail where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation

-- Once.Parser.Module.DeclTail.goTypeAliasB
d_goTypeAliasB_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_goTypeAliasB_10 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         (:) v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v6
                  -> let v7
                           = d_goTypeAliasB_10
                               (coe v0) (coe v5)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6) (coe v2)) in
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
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v13 v14 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v14)))
                                                           (coe (0 :: Integer)) (coe v5))
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v13 v14 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v14)))
                                                                 (coe (0 :: Integer)) (coe v5)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.Parser.Token.C_TEquals_24
                  -> let v6
                           = MAlonzo.Code.Once.Parser.Module.Core.d_parseTypeB'45'adapt_82
                               (coe v5)
                               (let v6
                                      = coe
                                          MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_86
                                          (coe v5) in
                                coe
                                  (case coe v6 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                     -> let v12
                                                              = coe
                                                                  MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_104
                                                                  (coe v8) (coe v10) in
                                                        coe
                                                          (case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                               -> case coe v13 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                      -> case coe v15 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                             -> let v18
                                                                                      = coe
                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174
                                                                                          v10 v8 v11
                                                                                          v17 in
                                                                                coe
                                                                                  (let v19
                                                                                         = coe
                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                             (coe
                                                                                                v14)
                                                                                             (coe
                                                                                                v16) in
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
                                                                                                                 = coe
                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                     v16
                                                                                                                     v14
                                                                                                                     v18
                                                                                                                     v24 in
                                                                                                           coe
                                                                                                             (let v26
                                                                                                                    = coe
                                                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                        (coe
                                                                                                                           v21)
                                                                                                                        (coe
                                                                                                                           v23) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v26 of
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                                                                     -> case coe
                                                                                                                               v27 of
                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                            -> case coe
                                                                                                                                      v29 of
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                   -> coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                           (coe
                                                                                                                                              v28)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                              (coe
                                                                                                                                                 v30)
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                 v23
                                                                                                                                                 v21
                                                                                                                                                 v25
                                                                                                                                                 v31)))
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                     -> coe
                                                                                                                          v26
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                          -> case coe
                                                                                                    v19 of
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                                                                 -> case coe
                                                                                                           v20 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                        -> case coe
                                                                                                                  v22 of
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                               -> let v25
                                                                                                                        = coe
                                                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                -> case coe
                                                                                                                                          v28 of
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                       -> coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  v27)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                  (coe
                                                                                                                                                     v29)
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                     v23
                                                                                                                                                     v21
                                                                                                                                                     v24
                                                                                                                                                     v30)))
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                         -> coe
                                                                                                                              v25
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                 -> coe
                                                                                                      v19
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                      -> case coe v13 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                             -> case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                    -> let v18
                                                                                             = coe
                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                 (coe
                                                                                                    v14)
                                                                                                 (coe
                                                                                                    v16) in
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
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                         v16
                                                                                                                         v14
                                                                                                                         v17
                                                                                                                         v23 in
                                                                                                               coe
                                                                                                                 (let v25
                                                                                                                        = coe
                                                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                            (coe
                                                                                                                               v20)
                                                                                                                            (coe
                                                                                                                               v22) in
                                                                                                                  coe
                                                                                                                    (case coe
                                                                                                                            v25 of
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                                                                         -> case coe
                                                                                                                                   v26 of
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                                                                                -> case coe
                                                                                                                                          v28 of
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                                                                                       -> coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  v27)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                  (coe
                                                                                                                                                     v29)
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                     v22
                                                                                                                                                     v20
                                                                                                                                                     v24
                                                                                                                                                     v30)))
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                         -> coe
                                                                                                                              v25
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> case coe
                                                                                                        v18 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> case coe
                                                                                                                      v21 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                                   -> let v24
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                    -> case coe
                                                                                                                                              v27 of
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                   (coe
                                                                                                                                                      v26)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                      (coe
                                                                                                                                                         v28)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                         v22
                                                                                                                                                         v20
                                                                                                                                                         v23
                                                                                                                                                         v29)))
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                             -> coe
                                                                                                                                  v24
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v18
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                             -> case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                           -> let v18
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                        (coe
                                                                                                           v14)
                                                                                                        (coe
                                                                                                           v16) in
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
                                                                                                                   -> coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v20)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v22)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                 v16
                                                                                                                                 v14
                                                                                                                                 v17
                                                                                                                                 v23)))
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v18
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v12
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> case coe v6 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                              -> case coe v7 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                     -> case coe v9 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                            -> let v12
                                                                     = coe
                                                                         MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                         (coe v8) (coe v10) in
                                                               coe
                                                                 (case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                      -> case coe v13 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                             -> case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                    -> let v18
                                                                                             = coe
                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                 v10
                                                                                                 v8
                                                                                                 v11
                                                                                                 v17 in
                                                                                       coe
                                                                                         (let v19
                                                                                                = coe
                                                                                                    MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                    (coe
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       v16) in
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
                                                                                                                             MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                             v16
                                                                                                                             v14
                                                                                                                             v18
                                                                                                                             v24)))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                 -> coe
                                                                                                      v19
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                             -> case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                           -> let v18
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                        (coe
                                                                                                           v14)
                                                                                                        (coe
                                                                                                           v16) in
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
                                                                                                                   -> coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v20)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v22)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                 v16
                                                                                                                                 v14
                                                                                                                                 v17
                                                                                                                                 v23)))
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v18
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v12
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                              -> case coe v6 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                            -> case coe v9 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                                   -> let v12
                                                                            = coe
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                (coe v8)
                                                                                (coe v10) in
                                                                      coe
                                                                        (case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                             -> case coe v13 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                           -> coe
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      v14)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         v16)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                         v10
                                                                                                         v8
                                                                                                         v11
                                                                                                         v17)))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v12
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> coe v6
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40
                                                     (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_reverse_444
                                                        v2)
                                                     (coe v8))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v12 v13 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v13)))
                                                           (coe (0 :: Integer)) (coe v5))
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe
                                                                    (\ v12 v13 ->
                                                                       addInt
                                                                         (coe (1 :: Integer))
                                                                         (coe v13)))
                                                                 (coe (0 :: Integer)) (coe v5)))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3
         _ -> coe v3)
-- Once.Parser.Module.DeclTail.parseTypeAliasB
d_parseTypeAliasB_76 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAliasB_76 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = d_goTypeAliasB_10
                                      (coe v3) (coe v5)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
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
                                                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                  (coe
                                                                     (\ v13 v14 ->
                                                                        addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v14)))
                                                                  (coe (0 :: Integer)) (coe v5))
                                                               (coe v12) (coe v6))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.DeclTail.parseTypeAlias
d_parseTypeAlias_120 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeAlias_120 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7
                                  = d_goTypeAliasB_10
                                      (coe v3) (coe v5)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
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
                                                         (coe v9) (coe v11))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v7 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v9) (coe v11))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
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
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                        (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.DeclTail.parsePrimitiveB
d_parsePrimitiveB_138 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePrimitiveB_138 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              (:) v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Parser.Token.C_TColon_22
                                       -> let v9
                                                = MAlonzo.Code.Once.Parser.Module.Core.d_parseTypeB'45'adapt_82
                                                    (coe v8)
                                                    (let v9
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_86
                                                               (coe v8) in
                                                     coe
                                                       (case coe v9 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                          -> let v15
                                                                                   = coe
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_104
                                                                                       (coe v11)
                                                                                       (coe v13) in
                                                                             coe
                                                                               (case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                    -> case coe
                                                                                              v16 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                           -> case coe
                                                                                                     v18 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                  -> let v21
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174
                                                                                                               v13
                                                                                                               v11
                                                                                                               v14
                                                                                                               v20 in
                                                                                                     coe
                                                                                                       (let v22
                                                                                                              = coe
                                                                                                                  MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                                  (coe
                                                                                                                     v17)
                                                                                                                  (coe
                                                                                                                     v19) in
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
                                                                                                                                      = coe
                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                                          v19
                                                                                                                                          v17
                                                                                                                                          v21
                                                                                                                                          v27 in
                                                                                                                                coe
                                                                                                                                  (let v29
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                             (coe
                                                                                                                                                v24)
                                                                                                                                             (coe
                                                                                                                                                v26) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v29 of
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                          -> case coe
                                                                                                                                                    v30 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                 -> case coe
                                                                                                                                                           v32 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                        -> coe
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                (coe
                                                                                                                                                                   v31)
                                                                                                                                                                (coe
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                   (coe
                                                                                                                                                                      v33)
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                      v26
                                                                                                                                                                      v24
                                                                                                                                                                      v28
                                                                                                                                                                      v34)))
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                          -> coe
                                                                                                                                               v29
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                               -> case coe
                                                                                                                         v22 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                                      -> case coe
                                                                                                                                v23 of
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                             -> case coe
                                                                                                                                       v25 of
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                    -> let v28
                                                                                                                                             = coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                                     -> case coe
                                                                                                                                                               v31 of
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                            -> coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       v30)
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          v32)
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                          v26
                                                                                                                                                                          v24
                                                                                                                                                                          v27
                                                                                                                                                                          v33)))
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> coe
                                                                                                                                                   v28
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                      -> coe
                                                                                                                           v22
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> case coe
                                                                                                            v18 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                         -> let v21
                                                                                                                  = coe
                                                                                                                      MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                                      (coe
                                                                                                                         v17)
                                                                                                                      (coe
                                                                                                                         v19) in
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
                                                                                                                                 -> let v27
                                                                                                                                          = coe
                                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                                              v19
                                                                                                                                              v17
                                                                                                                                              v20
                                                                                                                                              v26 in
                                                                                                                                    coe
                                                                                                                                      (let v28
                                                                                                                                             = coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                                 (coe
                                                                                                                                                    v23)
                                                                                                                                                 (coe
                                                                                                                                                    v25) in
                                                                                                                                       coe
                                                                                                                                         (case coe
                                                                                                                                                 v28 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                              -> case coe
                                                                                                                                                        v29 of
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                     -> case coe
                                                                                                                                                               v31 of
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                            -> coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       v30)
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          v32)
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                          v25
                                                                                                                                                                          v23
                                                                                                                                                                          v27
                                                                                                                                                                          v33)))
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> coe
                                                                                                                                                   v28
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                   -> case coe
                                                                                                                             v21 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                                                          -> case coe
                                                                                                                                    v22 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                                                 -> case coe
                                                                                                                                           v24 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                        -> let v27
                                                                                                                                                 = coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                                     (coe
                                                                                                                                                        v23)
                                                                                                                                                     (coe
                                                                                                                                                        v25) in
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
                                                                                                                                                                -> coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                        (coe
                                                                                                                                                                           v29)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              v31)
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                              v25
                                                                                                                                                                              v23
                                                                                                                                                                              v26
                                                                                                                                                                              v32)))
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                  -> coe
                                                                                                                                                       v27
                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> let v21
                                                                                                                         = coe
                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                             (coe
                                                                                                                                v17)
                                                                                                                             (coe
                                                                                                                                v19) in
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
                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                      v19
                                                                                                                                                      v17
                                                                                                                                                      v20
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> case coe v9 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                   -> case coe v10 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                          -> case coe v12 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                 -> let v15
                                                                                          = coe
                                                                                              MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                              (coe
                                                                                                 v11)
                                                                                              (coe
                                                                                                 v13) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> case coe
                                                                                                            v18 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                         -> let v21
                                                                                                                  = coe
                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                      v13
                                                                                                                      v11
                                                                                                                      v14
                                                                                                                      v20 in
                                                                                                            coe
                                                                                                              (let v22
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                         (coe
                                                                                                                            v17)
                                                                                                                         (coe
                                                                                                                            v19) in
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
                                                                                                                                    -> coe
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                            (coe
                                                                                                                                               v24)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  v26)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                  v19
                                                                                                                                                  v17
                                                                                                                                                  v21
                                                                                                                                                  v27)))
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                      -> coe
                                                                                                                           v22
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> let v21
                                                                                                                         = coe
                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                             (coe
                                                                                                                                v17)
                                                                                                                             (coe
                                                                                                                                v19) in
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
                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                      v19
                                                                                                                                                      v17
                                                                                                                                                      v20
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> case coe v9 of
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                          -> case coe v10 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                                 -> case coe v12 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                        -> let v15
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                     (coe
                                                                                                        v11)
                                                                                                     (coe
                                                                                                        v13) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                        (coe
                                                                                                                           v17)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v19)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                              v13
                                                                                                                              v11
                                                                                                                              v14
                                                                                                                              v20)))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                          -> coe v9
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError)) in
                                          coe
                                            (case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Module.Core.C_DPrimitive_38
                                                                          (coe v3) (coe v11))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                             (coe
                                                                                addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe
                                                                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                   (coe
                                                                                      (\ v15 v16 ->
                                                                                         addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v16)))
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe v8)))
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                (coe
                                                                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                   (coe
                                                                                      (\ v15 v16 ->
                                                                                         addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v16)))
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe v8))
                                                                                (coe v14)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                         (coe
                                                                                            (\ v15
                                                                                               v16 ->
                                                                                               addInt
                                                                                                 (coe
                                                                                                    (1 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    v16)))
                                                                                         (coe
                                                                                            (0 ::
                                                                                               Integer))
                                                                                         (coe
                                                                                            v8)))))
                                                                             (coe v6))))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe v9
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.DeclTail.parsePrimitive
d_parsePrimitive_184 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parsePrimitive_184 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              (:) v7 v8
                                -> case coe v7 of
                                     MAlonzo.Code.Once.Parser.Token.C_TColon_22
                                       -> let v9
                                                = MAlonzo.Code.Once.Parser.Module.Core.d_parseTypeB'45'adapt_82
                                                    (coe v8)
                                                    (let v9
                                                           = coe
                                                               MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_86
                                                               (coe v8) in
                                                     coe
                                                       (case coe v9 of
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                          -> let v15
                                                                                   = coe
                                                                                       MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_104
                                                                                       (coe v11)
                                                                                       (coe v13) in
                                                                             coe
                                                                               (case coe v15 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                    -> case coe
                                                                                              v16 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                           -> case coe
                                                                                                     v18 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                  -> let v21
                                                                                                           = coe
                                                                                                               MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174
                                                                                                               v13
                                                                                                               v11
                                                                                                               v14
                                                                                                               v20 in
                                                                                                     coe
                                                                                                       (let v22
                                                                                                              = coe
                                                                                                                  MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                                  (coe
                                                                                                                     v17)
                                                                                                                  (coe
                                                                                                                     v19) in
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
                                                                                                                                      = coe
                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                                          v19
                                                                                                                                          v17
                                                                                                                                          v21
                                                                                                                                          v27 in
                                                                                                                                coe
                                                                                                                                  (let v29
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                             (coe
                                                                                                                                                v24)
                                                                                                                                             (coe
                                                                                                                                                v26) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v29 of
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                                                          -> case coe
                                                                                                                                                    v30 of
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                                                                                 -> case coe
                                                                                                                                                           v32 of
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                                                                                        -> coe
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                (coe
                                                                                                                                                                   v31)
                                                                                                                                                                (coe
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                   (coe
                                                                                                                                                                      v33)
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                      v26
                                                                                                                                                                      v24
                                                                                                                                                                      v28
                                                                                                                                                                      v34)))
                                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                          -> coe
                                                                                                                                               v29
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                               -> case coe
                                                                                                                         v22 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                                      -> case coe
                                                                                                                                v23 of
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                             -> case coe
                                                                                                                                       v25 of
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                                    -> let v28
                                                                                                                                             = coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
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
                                                                                                                                                     -> case coe
                                                                                                                                                               v31 of
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                            -> coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       v30)
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          v32)
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                          v26
                                                                                                                                                                          v24
                                                                                                                                                                          v27
                                                                                                                                                                          v33)))
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> coe
                                                                                                                                                   v28
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                      -> coe
                                                                                                                           v22
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> case coe
                                                                                                            v18 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                         -> let v21
                                                                                                                  = coe
                                                                                                                      MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                                      (coe
                                                                                                                         v17)
                                                                                                                      (coe
                                                                                                                         v19) in
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
                                                                                                                                 -> let v27
                                                                                                                                          = coe
                                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                                              v19
                                                                                                                                              v17
                                                                                                                                              v20
                                                                                                                                              v26 in
                                                                                                                                    coe
                                                                                                                                      (let v28
                                                                                                                                             = coe
                                                                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                                 (coe
                                                                                                                                                    v23)
                                                                                                                                                 (coe
                                                                                                                                                    v25) in
                                                                                                                                       coe
                                                                                                                                         (case coe
                                                                                                                                                 v28 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                                                                              -> case coe
                                                                                                                                                        v29 of
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                                                                                     -> case coe
                                                                                                                                                               v31 of
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                                                                                            -> coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       v30)
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          v32)
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                          v25
                                                                                                                                                                          v23
                                                                                                                                                                          v27
                                                                                                                                                                          v33)))
                                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                              -> coe
                                                                                                                                                   v28
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                   -> case coe
                                                                                                                             v21 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                                                          -> case coe
                                                                                                                                    v22 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                                                                 -> case coe
                                                                                                                                           v24 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                                                                        -> let v27
                                                                                                                                                 = coe
                                                                                                                                                     MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                                     (coe
                                                                                                                                                        v23)
                                                                                                                                                     (coe
                                                                                                                                                        v25) in
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
                                                                                                                                                                -> coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                        (coe
                                                                                                                                                                           v29)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              v31)
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                                              v25
                                                                                                                                                                              v23
                                                                                                                                                                              v26
                                                                                                                                                                              v32)))
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                                                  -> coe
                                                                                                                                                       v27
                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> let v21
                                                                                                                         = coe
                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                             (coe
                                                                                                                                v17)
                                                                                                                             (coe
                                                                                                                                v19) in
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
                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                      v19
                                                                                                                                                      v17
                                                                                                                                                      v20
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            -> case coe v9 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                   -> case coe v10 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                          -> case coe v12 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                 -> let v15
                                                                                          = coe
                                                                                              MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                              (coe
                                                                                                 v11)
                                                                                              (coe
                                                                                                 v13) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v15 of
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                           -> case coe
                                                                                                     v16 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                  -> case coe
                                                                                                            v18 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                         -> let v21
                                                                                                                  = coe
                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                      v13
                                                                                                                      v11
                                                                                                                      v14
                                                                                                                      v20 in
                                                                                                            coe
                                                                                                              (let v22
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                         (coe
                                                                                                                            v17)
                                                                                                                         (coe
                                                                                                                            v19) in
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
                                                                                                                                    -> coe
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                            (coe
                                                                                                                                               v24)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  v26)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                  v19
                                                                                                                                                  v17
                                                                                                                                                  v21
                                                                                                                                                  v27)))
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                      -> coe
                                                                                                                           v22
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> let v21
                                                                                                                         = coe
                                                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                             (coe
                                                                                                                                v17)
                                                                                                                             (coe
                                                                                                                                v19) in
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
                                                                                                                                                      MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                      v19
                                                                                                                                                      v17
                                                                                                                                                      v20
                                                                                                                                                      v26)))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                          -> coe
                                                                                                                               v21
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> case coe v9 of
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                                          -> case coe v10 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                                 -> case coe v12 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                        -> let v15
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                     (coe
                                                                                                        v11)
                                                                                                     (coe
                                                                                                        v13) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                                                  -> case coe
                                                                                                            v16 of
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                                         -> case coe
                                                                                                                   v18 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                                -> coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                        (coe
                                                                                                                           v17)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v19)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                              v13
                                                                                                                              v11
                                                                                                                              v14
                                                                                                                              v20)))
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                  -> coe
                                                                                                       v15
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                          -> coe v9
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError)) in
                                          coe
                                            (case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> let v15
                                                                        = coe
                                                                            MAlonzo.Code.Once.Parser.Module.Core.C_DPrimitive_38
                                                                            (coe v3) (coe v11) in
                                                                  coe
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v15) (coe v13)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v11) (coe v13))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v9
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                        (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
