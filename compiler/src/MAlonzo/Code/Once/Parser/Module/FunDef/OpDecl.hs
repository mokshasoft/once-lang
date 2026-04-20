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

module MAlonzo.Code.Once.Parser.Module.FunDef.OpDecl where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Alloc
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Body
import qualified MAlonzo.Code.Once.Parser.Module.FunDef.Params
import qualified MAlonzo.Code.Once.Parser.Module.OpName
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation

-- Once.Parser.Module.FunDef.OpDecl.tryOpDeclAfterB
d_tryOpDeclAfterB_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryOpDeclAfterB_12 v0 v1
  = let v2
          = let v2
                  = MAlonzo.Code.Once.Parser.Module.FunDef.Body.d_parseFunBodyB_12
                      (coe v0)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (let v2
                                = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                    (coe v1) in
                          coe
                            (case coe v2 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                                 -> case coe v3 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                        -> case coe v5 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                               -> coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                       (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                          (coe v7)))
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 -> coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du_foldr_216
                                               (coe
                                                  (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                                               (coe (0 :: Integer)) (coe v1))))
                               _ -> MAlonzo.RTE.mazUnreachableError)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (let v2
                                         = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                             (coe v1) in
                                   coe
                                     (case coe v2 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                                          -> case coe v3 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                                 -> case coe v5 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe v4))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v6)
                                                                (coe
                                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                   (coe v7)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe
                                                           (\ v3 v4 ->
                                                              addInt (coe (1 :: Integer)) (coe v4)))
                                                        (coe (0 :: Integer)) (coe v1))))
                                        _ -> MAlonzo.RTE.mazUnreachableError))))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (let v2
                                            = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                                (coe v1) in
                                      coe
                                        (case coe v2 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                                             -> case coe v3 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                                    -> case coe v5 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe v4))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v6)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                      (coe v7)))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v2)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v3 v4 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v4)))
                                                           (coe (0 :: Integer)) (coe v1))))
                                           _ -> MAlonzo.RTE.mazUnreachableError))))))) in
            coe
              (let v3
                     = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Parser.Module.FunDef.Params.d_parseParamsB_26
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (let v3
                                            = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                                (coe v1) in
                                      coe
                                        (case coe v3 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                                             -> case coe v4 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                                    -> case coe v6 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe v5))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v7)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                      (coe v8)))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe
                                                              (\ v4 v5 ->
                                                                 addInt
                                                                   (coe (1 :: Integer)) (coe v5)))
                                                           (coe (0 :: Integer)) (coe v1))))
                                           _ -> MAlonzo.RTE.mazUnreachableError)))))) in
               coe
                 (let v4
                        = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (let v4
                                      = MAlonzo.Code.Once.Parser.Module.Alloc.d_parseAllocB_10
                                          (coe v1) in
                                coe
                                  (case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                       -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                              -> case coe v7 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe v6))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                (coe v9)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe
                                                        (\ v5 v6 ->
                                                           addInt (coe (1 :: Integer)) (coe v6)))
                                                     (coe (0 :: Integer)) (coe v1))))
                                     _ -> MAlonzo.RTE.mazUnreachableError))) in
                  coe
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> let v10
                                                = coe
                                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                    (coe
                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                                                       (coe v9) (coe v3))
                                                    (coe v4) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                        (coe v10)))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                                -> case coe v5 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v6)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                            (coe v9))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError))) in
    coe
      (case coe v1 of
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Parser.Token.C_TColon_22
                  -> let v5
                           = MAlonzo.Code.Once.Parser.Module.Core.d_parseTypeB'45'adapt_82
                               (coe v4)
                               (let v5
                                      = coe
                                          MAlonzo.Code.Once.Parser.Type.du_parseTypeAtomWF_86
                                          (coe v4) in
                                coe
                                  (case coe v5 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                       -> case coe v6 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                     -> let v11
                                                              = coe
                                                                  MAlonzo.Code.Once.Parser.Type.du_parseTypeProdTailWF_104
                                                                  (coe v7) (coe v9) in
                                                        coe
                                                          (case coe v11 of
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                      -> case coe v14 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                             -> let v17
                                                                                      = coe
                                                                                          MAlonzo.Code.Once.Parser.TypeRelation.C_pp'45'mk_174
                                                                                          v9 v7 v10
                                                                                          v16 in
                                                                                coe
                                                                                  (let v18
                                                                                         = coe
                                                                                             MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                             (coe
                                                                                                v13)
                                                                                             (coe
                                                                                                v15) in
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
                                                                                                                     v15
                                                                                                                     v13
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
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                               -> case coe v11 of
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                             -> case coe v14 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                    -> let v17
                                                                                             = coe
                                                                                                 MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                                                 (coe
                                                                                                    v13)
                                                                                                 (coe
                                                                                                    v15) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v17 of
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                              -> case coe
                                                                                                        v18 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                     -> case coe
                                                                                                               v20 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                            -> let v23
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                                         v15
                                                                                                                         v13
                                                                                                                         v16
                                                                                                                         v22 in
                                                                                                               coe
                                                                                                                 (let v24
                                                                                                                        = coe
                                                                                                                            MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                            (coe
                                                                                                                               v19)
                                                                                                                            (coe
                                                                                                                               v21) in
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
                                                                                                                                                     v21
                                                                                                                                                     v19
                                                                                                                                                     v23
                                                                                                                                                     v29)))
                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                         -> coe
                                                                                                                              v24
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                     -> case coe
                                                                                                               v18 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                            -> case coe
                                                                                                                      v20 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                   -> let v23
                                                                                                                            = coe
                                                                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                                                (coe
                                                                                                                                   v19)
                                                                                                                                (coe
                                                                                                                                   v21) in
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
                                                                                                                                           -> coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                   (coe
                                                                                                                                                      v25)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                      (coe
                                                                                                                                                         v27)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                                         v21
                                                                                                                                                         v19
                                                                                                                                                         v22
                                                                                                                                                         v28)))
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                             -> coe
                                                                                                                                  v23
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v17
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      -> case coe v11 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                             -> case coe v12 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> let v17
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                        (coe
                                                                                                           v13)
                                                                                                        (coe
                                                                                                           v15) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                     -> case coe
                                                                                                               v18 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                            -> case coe
                                                                                                                      v20 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                   -> coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v19)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v21)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                 v15
                                                                                                                                 v13
                                                                                                                                 v16
                                                                                                                                 v22)))
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v17
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v11
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> case coe v5 of
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                              -> case coe v6 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                            -> let v11
                                                                     = coe
                                                                         MAlonzo.Code.Once.Parser.Type.du_parseTypeSumTailWF_110
                                                                         (coe v7) (coe v9) in
                                                               coe
                                                                 (case coe v11 of
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                             -> case coe v14 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                    -> let v17
                                                                                             = coe
                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_ps'45'mk_206
                                                                                                 v9
                                                                                                 v7
                                                                                                 v10
                                                                                                 v16 in
                                                                                       coe
                                                                                         (let v18
                                                                                                = coe
                                                                                                    MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                    (coe
                                                                                                       v13)
                                                                                                    (coe
                                                                                                       v15) in
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
                                                                                                                             v15
                                                                                                                             v13
                                                                                                                             v17
                                                                                                                             v23)))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                 -> coe
                                                                                                      v18
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      -> case coe v11 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                             -> case coe v12 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> let v17
                                                                                                    = coe
                                                                                                        MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                                        (coe
                                                                                                           v13)
                                                                                                        (coe
                                                                                                           v15) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                                                     -> case coe
                                                                                                               v18 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                                            -> case coe
                                                                                                                      v20 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                                   -> coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v19)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                              (coe
                                                                                                                                 v21)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                                                 v15
                                                                                                                                 v13
                                                                                                                                 v16
                                                                                                                                 v22)))
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                     -> coe
                                                                                                          v17
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v11
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                              -> case coe v5 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                     -> case coe v6 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                            -> case coe v8 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                                   -> let v11
                                                                            = coe
                                                                                MAlonzo.Code.Once.Parser.Type.du_parseArrowTailWF_116
                                                                                (coe v7) (coe v9) in
                                                                      coe
                                                                        (case coe v11 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                             -> case coe v12 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                                    -> case coe
                                                                                              v14 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                           -> coe
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      v13)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                      (coe
                                                                                                         v15)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Parser.TypeRelation.C_pt'45'mk_238
                                                                                                         v9
                                                                                                         v7
                                                                                                         v10
                                                                                                         v16)))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe v11
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> coe v5
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                     (coe v0) (coe v7))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                              (coe
                                                                 (\ v11 v12 ->
                                                                    addInt
                                                                      (coe (1 :: Integer))
                                                                      (coe v12)))
                                                              (coe (0 :: Integer)) (coe v4))
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                    (coe
                                                                       (\ v11 v12 ->
                                                                          addInt
                                                                            (coe (1 :: Integer))
                                                                            (coe v12)))
                                                                    (coe (0 :: Integer))
                                                                    (coe v4))))))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.Module.FunDef.OpDecl.tryOpDeclAfter
d_tryOpDeclAfter_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryOpDeclAfter_58 v0 v1
  = let v2 = d_tryOpDeclAfterB_12 (coe v0) (coe v1) in
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
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.FunDef.OpDecl.tryOpDeclB
d_tryOpDeclB_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryOpDeclB_82 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.OpName.d_parseOperatorNameB_286
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = d_tryOpDeclAfterB_12 (coe v3) (coe v5) in
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
                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                               (coe v12) (coe v6))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.FunDef.OpDecl.tryOpDecl
d_tryOpDecl_126 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryOpDecl_126 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Module.OpName.d_parseOperatorNameB_286
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> let v7 = d_tryOpDeclAfterB_12 (coe v3) (coe v5) in
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
